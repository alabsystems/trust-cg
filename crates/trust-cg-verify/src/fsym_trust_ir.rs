// Symbolic execution: bounded trust_ir preflight scanner
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Bounded trust_ir-to-fsym preflight scanner.
//!
//! This module is intentionally narrow: it walks small acyclic functions with
//! direct branches and only evaluates concrete/value-known SSA expressions. It
//! only unrolls small loops when the CFG shape and trip count are statically
//! bounded. It does not invoke an SMT solver, summarize calls, or claim
//! corpus-level coverage.
//!
//! # What the scanner claims, and about which UB
//!
//! A function is CLEAN only when every reachable obligation of every UB class
//! in [`FSYM_TRUST_IR_UB_CLASSES`] marked `Checked` was discharged `Safe` on
//! every walked path. Each walked site owes one verdict per class it can raise
//! (`obligation_kinds`); a class the scanner cannot decide there is an Unknown
//! by name, never silence. The classes marked `NotChecked` are listed with the
//! reason they cannot make a scanned function wrongly clean (refused at
//! admission, or not UB in trust-ir).
//!
//! What a site can raise is not the scanner's opinion: it is DERIVED from
//! trust-ir's reference interpreter ([`crate::fsym_ub_map`], every place the
//! interpreter raises `UndefinedBehavior` and the instructions that reach it,
//! re-derived from the interpreter's source by `tests/fsym_ub_map.rs`). The
//! admission gate admits an instruction only if it owes a verdict for every
//! such UB, and the classes table is checked against the same map.
//!
//! A proof annotation (`NotNull`, `InBounds`) is a producer's CLAIM, and the
//! scanner never takes one for a proof. An annotation on an access through a
//! parameter is a claim about every caller — and nothing checks callers (an
//! entry function has none the scan can see: the harness hands it null, a
//! freed block, an address naming no allocation); one on an access through a
//! loaded pointer or a call's result is the same unchecked claim. Every
//! verdict is decided on the scanner's own facts, so an annotated access is
//! exactly as clean as the same access unannotated. (No producer in this
//! workspace emits `NotNull` / `InBounds` on a trust-ir access; the LLVM
//! importer's `InBounds` sits on GEPs, which were never taken as proofs.)
//!
//! # One layout authority: the reference interpreter's
//!
//! Every size, field offset, GEP stride, alignment and initialized byte the
//! scanner reasons with is the reference interpreter's own
//! ([`crate::fsym_layout`], a port of its layout functions held to it by
//! execution in `tests/fsym_layout.rs` and pinned to its source): a declared
//! struct layout is used verbatim, `<N x bool>` is a byte a lane, an
//! allocation with no explicit alignment is placed at its type's natural one,
//! a whole-aggregate store writes its padding and an inactive variant's tail
//! UNINITIALIZED. The native backends' layout is not consulted — the UB fsym
//! owes verdicts for is the interpreter's, over the interpreter's bytes. An
//! instruction that lays out a type the interpreter cannot is refused by
//! name, and so is every function of a module the interpreter does not
//! execute.
//!
//! # The run model, and the address the bump pointer reaches
//!
//! A verdict is about the runs of [`FSYM_RUN_MODEL`], and
//! [`FsymRunModel::breach`] decides whether a run is one: an entry
//! function's execution from fresh memory whose fuel is below 2^50 steps,
//! on entry arguments that name no allocation, runtime handle or nominal
//! function item outside the bounded value model.
//! Everything such a run allocates is allocated by the module's own code (an
//! `Alloca` / `HeapAlloc`, a `SeqMap` element cell, a global's first
//! materialization, at most once a global), in whatever function the entry
//! reaches, scanned or not. The bound is the MODEL's, not the interpreter's:
//! `InterpretOptions` is public, and an embedder can build any
//! `InterpretPointer`. The UB map names what a run outside the model raises
//! that no verdict covers (`fsym_ub_map::FORGED_ENTRY_POINTER`).
//!
//! The interpreter places an allocation by bumping a pointer, aligning it up
//! first: each placement advances it by its padding (less than its
//! alignment) plus its footprint, and by one byte when the footprint is zero.
//! Since trust-ir v50 the interpreter has NO memory budget (its storage is
//! sparse): a placement whose base or end would pass the address space is
//! refused as `OutOfMemory` — an incapacity of the model, never undefined
//! behaviour of the program — at every pointer width.
//!
//! fsym decides a placement only below [`FSYM_TRUST_IR_MAX_MODELED_FOOTPRINT`]
//! (2^62 bytes) and, at 64-bit pointers, only under the BUDGET premise: no
//! instruction of any function of the module may place past
//! [`FSYM_TRUST_IR_MAX_MODELED_ALIGN`] (or at an alignment fsym cannot lay
//! out), decided for the MODULE ([`budget_premise_violation`]) because a
//! per-function clean claim cannot rest on callers it does not see. Outside
//! either bound the placement is an Unknown by name. Both bounds were derived
//! when the interpreter faulted "base / next address overflow" as UB past a
//! memory budget; with that fault now `OutOfMemory` they only narrow what
//! fsym decides (a conservative Unknown), never what a verdict claims. An
//! object's end never passes 2^64 - 1 (the interpreter checks it), so a
//! pointer one past it has an address.
//!
//! * At 32-bit pointers the interpreter refuses (OutOfMemory) a placement
//!   whose last byte passes 2^32 - 1, so the pointer never passes 2^32: the
//!   base is at most `2^63` at any alignment, and a footprint below 2^62
//!   cannot overflow 64 bits from it. Safe with no premise and in every run,
//!   in the model or not. But no fuel keeps the pointer below 2^32 — 2^20
//!   zero-sized allocations at alignment 4096 reach it — so a non-empty
//!   object may END exactly at 2^32, where a pointer one past it has no
//!   address: a GEP to it or from it, and exposing it, are Unknown
//!   ([`ScanTarget::end_may_be_unnameable`]), and so is encoding a global
//!   initializer's pointer to a global's end.
//!
//! # The pointer model is ABSTRACT
//!
//! A pointer's facts (`PointerFacts`) separate what is known exactly from what
//! is only an abstraction:
//!
//! * `addr` is the pointer's run-time ADDRESS as an exact expression over the
//!   scan's free inputs — `0` for null, a constant for a constant address, the
//!   free variable of a parameter, plus exact GEP offsets. Only an exact
//!   address may be compared, cast to an integer, or decide null-ness.
//! * `object` is the tracked allocation a pointer points into (its
//!   provenance), `byte_offset` its offset from that allocation's base. An
//!   object id is an IDENTITY, never a value: its address is unknown, so
//!   `ptrtoint` of it, a comparison involving it, and every value computed
//!   from those are unmodeled (a branch on one walks both arms with no path
//!   fact), and no path is ever pruned on it.
//! * A pointer with no tracked provenance (a parameter, a loaded pointer, a
//!   constant or integer-cast address, a global) names no object the scanner
//!   knows the extent, lifetime, alignment or contents of: every access
//!   through it is an Unknown, whatever its address.
//! * `addr` is what the pointer's address IS when it has one; whether it has
//!   one (`PointerFacts::nameable`) is a separate fact. A 64-bit GEP moves an
//!   allocation OFFSET and faults only when that overflows, so a pointer can
//!   lie so far past its object that base + offset has no address — the
//!   interpreter faults only when something asks for it (`ptrtoint`, storing
//!   the pointer). A parameter may be such a pointer, and a GEP result is one
//!   unless its no-wrap is proven: exposing either is an Unknown.

use crate::fsym_arith::{ArithOp, ArithUbKind, check_arith_ub};
use crate::fsym_bounds::{BoundsOp, check_oob_ub};
use crate::fsym_layout::{ByteCoverage, FsymLayout, allocation_align, global_align};
use crate::fsym_null::{FsymVerdict, MemOp, PathContext, check_null_deref, guards_hold};
use crate::fsym_uaf::{UafEvent, UafEventKind, check_uaf_ub};
use crate::fsym_ub_map::fsym_map_refusal;
use crate::smt::{EvalResult, SmtExpr, SmtSort};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::path::Path;
use std::rc::Rc;
use std::sync::{Arc, Mutex, OnceLock};
use trust_cg_lower::adapter::{AdapterNamedCallSemantics, classify_adapter_direct_call};
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, FuncId, Function, ICmpOp, Inst, InstrNode, Linkage,
    Module, OverflowOp, SourceSpan, SwitchCase, Ty, UnOp, ValueId,
};

/// Maximum instruction count scanned in one bounded trust_ir preflight function.
///
/// Larger bodies are skipped so `--fsym` remains a bounded preflight rather than
/// an unbounded analysis pass.
pub const FSYM_TRUST_IR_MAX_STRAIGHT_LINE_INSTRUCTIONS: usize = 256;

/// Maximum basic block count scanned in one acyclic trust_ir preflight function.
pub const FSYM_TRUST_IR_MAX_BLOCKS: usize = 16;

/// Exact scope refusal used by the Char-validity regression/oracle controls.
/// Valid Char values are refused too: bounded fsym has no Unicode invariant.
pub const FSYM_CHAR_BINDING_REFUSAL: &str =
    "Char SSA bindings require Unicode scalar validity outside bounded fsym support";

/// Maximum explicit switch cases explored by the bounded trust_ir preflight.
pub const FSYM_TRUST_IR_MAX_SWITCH_CASES: usize = 8;

/// Maximum backedge traversals scanned for one statically bounded trust_ir loop.
pub const FSYM_TRUST_IR_MAX_LOOP_UNROLL_ITERATIONS: usize = 16;

const FSYM_TRUST_IR_MAX_LOOP_VALIDATION_STATES: usize =
    FSYM_TRUST_IR_MAX_BLOCKS * (FSYM_TRUST_IR_MAX_LOOP_UNROLL_ITERATIONS + 2) * 4;

/// Maximum path states (block visits) the walk of one function takes.
///
/// The walk forks at every undecided branch, so an acyclic CFG within the
/// block bound can still have exponentially many paths (a chain of `Switch`
/// blocks forks up to `FSYM_TRUST_IR_MAX_SWITCH_CASES + 1` ways per level).
/// Past this bound the walk stops and the function is an Unknown of kind
/// `ScanBound` by name: the paths it did not walk are unchecked, never clean.
pub const FSYM_TRUST_IR_MAX_PATH_STATES: usize = 4_096;

/// Largest tracked object (in bytes) whose per-byte initialization the
/// scanner follows. A load from a larger object, or from one whose size is
/// not a constant, is an `Uninitialized` Unknown.
const FSYM_TRUST_IR_MAX_INIT_TRACKED_BYTES: u64 = 4_096;

/// Largest placement alignment (bytes) the 64-bit BUDGET premise admits (see
/// the module docs). Past it an allocation's base may land where
/// `base + size` overflows 64 bits (the reference interpreter faults "base
/// address overflow"), so at 64-bit pointers such an `Alloca` / `HeapAlloc`
/// owes an Unknown.
pub(crate) const FSYM_TRUST_IR_MAX_MODELED_ALIGN: u64 = 4_096;

/// The runs a verdict is about (see the module docs, "The run model"): a
/// reference-interpreter run from fresh memory within these bounds, on
/// entry arguments [`FsymRunModel::breach`] admits.
///
/// There is no memory bound: since trust-ir v50 the interpreter has no
/// memory budget (its storage is sparse), and a placement that exhausts the
/// address space is `OutOfMemory` — an incapacity of the model — never
/// undefined behaviour of the program.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FsymRunModel {
    /// A run's `InterpretOptions::fuel` is below this many steps.
    pub fuel_limit: u64,
}

/// fsym's run model: fuel below 2^50 steps.
pub const FSYM_RUN_MODEL: FsymRunModel = FsymRunModel {
    fuel_limit: 1 << 50,
};

impl FsymRunModel {
    /// Why a run with `options` on the entry arguments `args` is outside the
    /// model, or `None` when it is inside: a fuel at or past the model's
    /// bound, or an entry argument carrying an allocation pointer or a
    /// runtime handle (a run starts from fresh memory and host state, so an
    /// embedder made it) or a trust-ir v49 unwritten aggregate lane (fsym
    /// models none), or a nominal function item whose target semantics are
    /// outside the bounded value model. Past the fuel bound a run makes placements the BUDGET
    /// premise does not count, and a forged pointer or handle may name what
    /// the run never made: no verdict covers such a run. The run model is
    /// also the panic=abort projection (trust-ir v56,
    /// `PanicStrategy::Abort`, the interpreter's default): fsym scans a
    /// failed check as the run's end, and trust-ir states that a verdict
    /// computed under `Abort` covers panic=abort only; under
    /// `PanicStrategy::Unwind` a callee's landing pad may resume a run the
    /// abort projection ended, so no verdict covers an `Unwind` run.
    pub fn breach(
        &self,
        options: &trust_ir::InterpretOptions,
        args: &[trust_ir::InterpretValue],
    ) -> Option<String> {
        if options.fuel >= self.fuel_limit {
            return Some(format!(
                "a fuel of {} steps is not below the run model's {}",
                options.fuel, self.fuel_limit
            ));
        }
        // EXHAUSTIVE on purpose: a strategy added to trust-ir fails to
        // compile here until it is placed.
        match options.panic_strategy {
            trust_ir::interpret::PanicStrategy::Abort => {}
            trust_ir::interpret::PanicStrategy::Unwind => {
                return Some(
                    "the panic strategy is Unwind; the run model is the panic=abort projection"
                        .to_string(),
                );
            }
        }
        args.iter().enumerate().find_map(|(index, arg)| {
            forged_part(arg).map(|what| format!("entry argument {index} carries {what}"))
        })
    }
}

/// A part of an entry argument outside the bounded run model, including an
/// allocation pointer, runtime handle, nominal item or unwritten aggregate lane.
/// EXHAUSTIVE on purpose: a value kind added to trust-ir fails to compile here
/// until it is placed.
fn forged_part(value: &trust_ir::InterpretValue) -> Option<&'static str> {
    use trust_ir::InterpretValueKind as V;
    match &value.kind {
        V::Ptr(_) => Some("a pointer naming an allocation"),
        V::Handle { .. } => Some("a runtime handle"),
        V::Tensor { .. } => Some("a tensor value outside the bounded model"),
        V::FnItem(_) => Some("a nominal function item outside the bounded model"),
        // trust-ir v50: array and vector values are ropes; trust-ir f9a59d5e
        // made sequence and set values the same persistent ropes. Each STORED
        // value is visited once (a splat's element once, whatever its length):
        // a forged part in any lane is one in a stored value.
        V::Vector(values) | V::Array(values) | V::Sequence(values) | V::Set(values) => {
            let found = values.try_for_each_stored(|value| match forged_part(value) {
                Some(what) => std::ops::ControlFlow::Break(what),
                None => std::ops::ControlFlow::Continue(()),
            });
            match found {
                std::ops::ControlFlow::Break(what) => Some(what),
                std::ops::ControlFlow::Continue(()) => None,
            }
        }
        V::Aggregate(values)
        | V::Closure {
            captures: values, ..
        } => values.iter().find_map(forged_part),
        V::Record(fields) => fields.iter().find_map(|(_, value)| forged_part(value)),
        V::FatPtr { data, metadata } => forged_part(data).or_else(|| forged_part(metadata)),
        V::Frame { slots, .. } => slots.iter().flatten().find_map(forged_part),
        V::Int(_)
        | V::FloatBits(_)
        | V::Bool(_)
        | V::FnDef(_)
        | V::PhantomData
        | V::NullPtr
        | V::Unit
        | V::PartialBytes(_)
        | V::DanglingPtr(_) => None,
        // v49: fsym models no unwritten lane (`module_unwritten_lane`), so a
        // run handed one is outside the model.
        V::Uninit => Some("an unwritten aggregate lane (uninit)"),
    }
}

/// The largest allocation footprint a placement verdict is decided for,
/// exclusive (2^62 bytes). A placement whose own footprint (its size, plus
/// the heap's 16-byte usable-size slack) reaches it is placed or refused
/// (OutOfMemory, the address space exhausted) depending on where the run's
/// earlier placements left the bump pointer, which the scan does not bound:
/// it owes an Unknown by name at any pointer width, never a verdict. This
/// bounds what fsym DECIDES, not what a program may allocate — the
/// interpreter has no memory budget and never refuses a placement for size
/// alone.
pub(crate) const FSYM_TRUST_IR_MAX_MODELED_FOOTPRINT: u64 = 1 << 62;

/// The reference interpreter's usable-size slack past a `HeapAlloc`'s
/// requested bytes (`HEAP_USABLE_SLACK`): part of its footprint.
const FSYM_TRUST_IR_HEAP_SLACK: u64 = 16;

/// Severity used when rendering fsym diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FsymTrustIrSeverity {
    Warning,
    Error,
}

impl FsymTrustIrSeverity {
    fn as_str(self) -> &'static str {
        match self {
            FsymTrustIrSeverity::Warning => "warning",
            FsymTrustIrSeverity::Error => "error",
        }
    }
}

/// Concrete UB class reported by the trust_ir fsym preflight.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FsymTrustIrDiagnosticKind {
    NullDeref,
    /// Division / remainder by zero or `INT_MIN / -1`, signed overflow (the
    /// source-level trap reading), an out-of-range shift amount, a
    /// non-positive or overflowing allocation count, and a raw float-to-integer
    /// conversion of NaN or an out-of-range value.
    Arithmetic,
    /// An access outside its object's extent, or through a pointer with no
    /// tracked provenance (whose object's extent the scanner cannot know) — a
    /// borrow of one included; and an aggregate lane or vector element
    /// outside the value's shape (an enum lane of an inactive variant, an
    /// element index past the lane count).
    OutOfBounds,
    /// A load, store or free of an allocation already freed (use after free,
    /// double free), or of one a call may have freed.
    UseAfterFree,
    /// Overlapping source and destination ranges of a non-overlapping
    /// (`memcpy`-semantics) `Inst::MemCopy`, which trust-ir defines as UB.
    Overlap,
    /// A direct call whose memory effects the scanner cannot account for: a
    /// body-less (external) callee handed a pointer-carrying argument, a
    /// bodied callee the scanner refuses to scan, or a callee that does not
    /// resolve in the scanned module. Only ever an Unknown — never a concrete
    /// diagnostic and never a pass.
    UnsummarizedCall,
    /// A `Dealloc` of something that is not the base of a live heap
    /// allocation: null, a stack (`Alloca`) object, an interior pointer, or a
    /// pointer the scanner cannot tie to one.
    InvalidFree,
    /// GEP address arithmetic trust-ir defines as UB: a null base, a negative
    /// signed index, an offset that overflows, an address past the target's
    /// address space.
    PointerArithmetic,
    /// An access whose address is not a multiple of its alignment (explicit,
    /// or the accessed type's natural alignment).
    Misaligned,
    /// A load that may read bytes never written (poison the loaded value
    /// carries; inspecting it is UB). Only ever an Unknown.
    Uninitialized,
    /// An `unreachable` terminator the walk reaches.
    UnreachableReached,
    /// The walk of the function hit `FSYM_TRUST_IR_MAX_PATH_STATES`: the paths
    /// past it are unchecked. Only ever an Unknown.
    ScanBound,
}

impl FsymTrustIrDiagnosticKind {
    fn as_str(self) -> &'static str {
        match self {
            FsymTrustIrDiagnosticKind::NullDeref => "null-deref",
            FsymTrustIrDiagnosticKind::Arithmetic => "arithmetic",
            FsymTrustIrDiagnosticKind::OutOfBounds => "bounds",
            FsymTrustIrDiagnosticKind::UseAfterFree => "use-after-free",
            FsymTrustIrDiagnosticKind::Overlap => "overlap",
            FsymTrustIrDiagnosticKind::UnsummarizedCall => "unsummarized-call",
            FsymTrustIrDiagnosticKind::InvalidFree => "invalid-free",
            FsymTrustIrDiagnosticKind::PointerArithmetic => "pointer-arithmetic",
            FsymTrustIrDiagnosticKind::Misaligned => "misaligned",
            FsymTrustIrDiagnosticKind::Uninitialized => "uninitialized-read",
            FsymTrustIrDiagnosticKind::UnreachableReached => "unreachable-reached",
            FsymTrustIrDiagnosticKind::ScanBound => "scan-bound",
        }
    }
}

/// Whether the bounded scanner checks a UB class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FsymUbClassStatus {
    /// Every reachable obligation of the class owes a verdict (Safe, a
    /// diagnostic, or an Unknown); `kind` names it in the report.
    Checked(FsymTrustIrDiagnosticKind),
    /// Not checked. `FsymUbClass::detail` says why that cannot make a scanned
    /// function wrongly clean.
    NotChecked,
}

/// One class of undefined behaviour and the scanner's stance on it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FsymUbClass {
    pub name: &'static str,
    pub status: FsymUbClassStatus,
    pub detail: &'static str,
}

/// The UB classes of trust-ir and what the bounded scanner does about each.
///
/// CHECKED AGAINST THE INTERPRETER: every place trust-ir's reference
/// interpreter raises `UndefinedBehavior` is an entry of
/// `fsym_ub_map::FSYM_INTERPRETER_UB_SITES` naming one of these classes, and
/// `tests/fsym_ub_map.rs` requires (a) every site's class to be listed here;
/// (b) a class with a site that fsym owes a verdict for (at the raising
/// instruction or at the value's source) to be `Checked`, with that verdict's
/// kind among the `Checked` kinds; (c) a `NotChecked` class to have only sites
/// refused at admission, not raised in a scanned function, or outside a
/// scanned body — so this table can never claim a class impossible or refused
/// while an admitted instruction raises it. A CLEAN function is clean with
/// respect to the `Checked` classes.
pub const FSYM_TRUST_IR_UB_CLASSES: &[FsymUbClass] = &[
    FsymUbClass {
        name: "typed ABI attributes and provenance",
        status: FsymUbClassStatus::NotChecked,
        detail: "modules containing any typed signature ABI are refused before scanning, so no typed-ABI transport or provenance rule is claimed by bounded fsym",
    },
    FsymUbClass {
        name: "enum byte-image validity",
        status: FsymUbClassStatus::NotChecked,
        detail: "loads and casts that reconstruct or encode an enum-containing byte image are refused at admission; bounded fsym tracks initialized coverage but does not prove a discriminant denotes an inhabited variant",
    },
    FsymUbClass {
        name: "tensor gather/scatter coordinates and extents",
        status: FsymUbClassStatus::NotChecked,
        detail: "TensorGather and TensorScatter (trust-ir v69) are refused at admission; coordinate-tensor extent agreement and per-axis coordinate bounds have no bounded fsym model",
    },
    FsymUbClass {
        name: "tensor map/reduce/view shapes and indices",
        status: FsymUbClassStatus::NotChecked,
        detail: "TensorMap, TensorReduce and TensorView are refused at admission; their tensor lanes, coordinate functions and extents have no bounded fsym model",
    },
    FsymUbClass {
        name: "tensor contraction shapes",
        status: FsymUbClassStatus::NotChecked,
        detail: "TensorContract is refused at admission; tensor extent agreement and result cardinality have no bounded fsym model",
    },
    FsymUbClass {
        name: "Unicode scalar validity",
        status: FsymUbClassStatus::NotChecked,
        detail: "functions with Char SSA bindings (block parameters or instruction results, including dead and discarded results) are refused by name before scanning; unresolved result typing is refused, never interpreted as absence of Char",
    },
    FsymUbClass {
        name: "null dereference",
        status: FsymUbClassStatus::Checked(FsymTrustIrDiagnosticKind::NullDeref),
        detail: "every Load/Store/atomic/bulk access, a GEP base and a borrowed pointer must be provably non-null (a Dealloc of null is an invalid free); a NotNull annotation is a claim, never a proof",
    },
    FsymUbClass {
        name: "out of bounds / no provenance",
        status: FsymUbClassStatus::Checked(FsymTrustIrDiagnosticKind::OutOfBounds),
        detail: "an access must lie inside a tracked object, sized by the reference interpreter's layout; one through a pointer with no tracked provenance (and a borrow of one) is Unknown, as is a bulk count the scanner cannot bound; an InBounds annotation is a claim, never a proof",
    },
    FsymUbClass {
        name: "aggregate lanes and vector elements",
        status: FsymUbClassStatus::Checked(FsymTrustIrDiagnosticKind::OutOfBounds),
        detail: "ExtractField/InsertField: a lane of the aggregate's shape - for an enum, a field of its ACTIVE variant (tracked from Const/MakeAggregate, else Unknown unless every variant agrees) and never the tag on insert; ExtractElement/InsertElement: an index in [0, len)",
    },
    FsymUbClass {
        name: "use after free / double free",
        status: FsymUbClassStatus::Checked(FsymTrustIrDiagnosticKind::UseAfterFree),
        detail: "tracked objects follow a per-path lifetime stream; a call handed an object, or a free of an untracked pointer, makes later lifetimes Unknown",
    },
    FsymUbClass {
        name: "invalid free",
        status: FsymUbClassStatus::Checked(FsymTrustIrDiagnosticKind::InvalidFree),
        detail: "Dealloc must name the base of a live RustHeap/CMalloc heap allocation under no live borrow (null, stack, interior, a reference-counted SwiftHeap/CleanHeap cell: diagnostics; untracked, freed on a path that borrowed, or reachable by an earlier call: Unknown)",
    },
    FsymUbClass {
        name: "misaligned access",
        status: FsymUbClassStatus::Checked(FsymTrustIrDiagnosticKind::Misaligned),
        detail: "decided from a tracked object's base alignment and a concrete offset; otherwise Unknown (bulk accesses are byte-granular)",
    },
    FsymUbClass {
        name: "uninitialized read and poison inspection",
        status: FsymUbClassStatus::Checked(FsymTrustIrDiagnosticKind::Uninitialized),
        detail: "per-byte initialization of tracked objects up to 4096 bytes, written as the interpreter writes it (a whole-aggregate store leaves padding and an inactive variant's tail uninitialized); any load not proven initialized is Unknown - the only poison source a scanned function has (Undef and LoadSlot are refused), so inspecting poison is owed where it is made",
    },
    FsymUbClass {
        name: "memcpy overlap",
        status: FsymUbClassStatus::Checked(FsymTrustIrDiagnosticKind::Overlap),
        detail: "non-overlapping MemCopy and memcpy calls",
    },
    FsymUbClass {
        name: "integer arithmetic",
        status: FsymUbClassStatus::Checked(FsymTrustIrDiagnosticKind::Arithmetic),
        detail: "div/rem by zero and INT_MIN/-1, shift amount >= width (ShiftInRange), and - stricter than trust-ir's wrapping - signed add/sub/mul/neg overflow",
    },
    FsymUbClass {
        name: "float-to-integer conversion",
        status: FsymUbClassStatus::Checked(FsymTrustIrDiagnosticKind::Arithmetic),
        detail: "FPToSI/FPToUI of NaN or a value outside the destination's range: decided for a constant operand, otherwise Unknown (the saturating casts are total)",
    },
    FsymUbClass {
        name: "allocation size and placement",
        status: FsymUbClassStatus::Checked(FsymTrustIrDiagnosticKind::Arithmetic),
        detail: "Alloca/HeapAlloc count <= 0, past u64, or a size that overflows (sizes are the reference interpreter's layout); a placement alignment past 4096 - explicit, else the type's natural one - is Unknown, as is materializing a module global placed past it (GlobalAddr, a Const addressing a symbol), and so is a placement of 2^62 bytes or more; every other placement is decided for runs in the run model (FSYM_RUN_MODEL: fuel below 2^50 steps)",
    },
    FsymUbClass {
        name: "pointer arithmetic and address exposure",
        status: FsymUbClassStatus::Checked(FsymTrustIrDiagnosticKind::PointerArithmetic),
        detail: "GEP: negative signed index, offset overflow, address past a 32-bit address space (a solver candidate encodes the target's limit, and none is attached where the base is abstract); ptrtoint, storing an address-holding value, inttoptr, a global initializer's addresses: the address must be representable",
    },
    FsymUbClass {
        name: "reaching unreachable",
        status: FsymUbClassStatus::Checked(FsymTrustIrDiagnosticKind::UnreachableReached),
        detail: "an `unreachable` on a walked path is UB unless an earlier call does not return (then Unknown)",
    },
    FsymUbClass {
        name: "unsummarized call effects",
        status: FsymUbClassStatus::Checked(FsymTrustIrDiagnosticKind::UnsummarizedCall),
        detail: "every call owes a verdict; a module-bound callee's body is checked by its own scan (a caller is UB-free only if its callees are clean); an external, link-replaceable, unresolved or refused callee handed a pointer is Unknown",
    },
    FsymUbClass {
        name: "undef, ARC, binding frames, dialect ops, indirect calls, SeqMap, unwinding, coroutines",
        status: FsymUbClassStatus::NotChecked,
        detail: "refused at admission by name (UnsupportedInstruction / UnsupportedTerminator); borrow permissions are not tracked, so a free that may be under a live borrow is an InvalidFree Unknown (see invalid free)",
    },
    FsymUbClass {
        name: "host runtime handles and host models",
        status: FsymUbClassStatus::NotChecked,
        detail: "raised only for the harness's entry arguments or by a host model serving a body-less function; a scanned body reaches one only through a call, whose pointer or handle arguments make it an UnsummarizedCall Unknown",
    },
    FsymUbClass {
        name: "data races / atomic ordering",
        status: FsymUbClassStatus::NotChecked,
        detail: "no interpreter UB: trust-ir's executable model is single-threaded; DataRaceFree is asserted, never checked, in trust-ir itself",
    },
    FsymUbClass {
        name: "floating-point arithmetic",
        status: FsymUbClassStatus::NotChecked,
        detail: "no interpreter UB: IEEE operations yield NaN and infinities as values (float-to-integer conversion is its own, checked class)",
    },
    FsymUbClass {
        name: "false Assume",
        status: FsymUbClassStatus::NotChecked,
        detail: "not UB in trust-ir (the reference interpreter reports AssumeViolated); the scanner takes the condition as a path fact",
    },
];

/// One concrete UB diagnostic emitted by the bounded preflight.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsymTrustIrDiagnostic {
    pub kind: FsymTrustIrDiagnosticKind,
    pub module: String,
    pub function: String,
    pub block: u32,
    pub inst_index: usize,
    pub span: Option<SourceSpan>,
    pub message: String,
    pub witness: Vec<(String, u64)>,
}

impl FsymTrustIrDiagnostic {
    /// Render this diagnostic in the CLI's `warning[fsym]` / `error[fsym]`
    /// style. The optional input path is display-only provenance.
    pub fn render(&self, severity: FsymTrustIrSeverity, input: Option<&Path>) -> String {
        let mut out = format!("{}[fsym]: ", severity.as_str());
        if let Some(input) = input {
            out.push_str(&format!("{}: ", input.display()));
        }
        out.push_str(&format!(
            "{} in module `{}` function `{}` bb{} inst{}: {}",
            self.kind.as_str(),
            self.module,
            self.function,
            self.block,
            self.inst_index,
            self.message
        ));

        if let Some(span) = self.span {
            out.push_str(&format!(
                " (source file {} line {} col {})",
                span.file, span.line, span.col
            ));
        }

        if !self.witness.is_empty() {
            let witness = self
                .witness
                .iter()
                .map(|(name, value)| format!("{name}={value}"))
                .collect::<Vec<_>>()
                .join(", ");
            out.push_str(&format!("; witness: {witness}"));
        }

        out
    }
}

/// Reason a function was not scanned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FsymTrustIrSkipReason {
    Loop,
    Switch,
    TooLarge,
    MalformedCfg,
    UnsupportedTerminator,
    UnsupportedInstruction,
    /// The function's semantics depend on the target pointer width (it has a
    /// `Usize`/`Isize` value) and the module does not pin one the scanner
    /// models, or the module pins a pointer width/layout outside the
    /// scanner's modeled targets.
    PointerWidth,
}

impl FsymTrustIrSkipReason {
    fn as_str(self) -> &'static str {
        match self {
            FsymTrustIrSkipReason::Loop => "loop",
            FsymTrustIrSkipReason::Switch => "switch",
            FsymTrustIrSkipReason::TooLarge => "too-large",
            FsymTrustIrSkipReason::MalformedCfg => "malformed-cfg",
            FsymTrustIrSkipReason::UnsupportedTerminator => "unsupported-terminator",
            FsymTrustIrSkipReason::UnsupportedInstruction => "unsupported-instruction",
            FsymTrustIrSkipReason::PointerWidth => "pointer-width",
        }
    }
}

/// One bounded-preflight skip emitted for a function outside fsym scope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsymTrustIrSkip {
    pub function: String,
    pub reason: FsymTrustIrSkipReason,
    pub detail: String,
}

impl FsymTrustIrSkip {
    /// Render this skip as a stable warning diagnostic.
    pub fn render(&self, input: Option<&Path>) -> String {
        let mut out = "warning[fsym]: ".to_string();
        if let Some(input) = input {
            out.push_str(&format!("{}: ", input.display()));
        }
        out.push_str(&format!(
            "skipped function `{}` reason={} detail={}",
            self.function,
            self.reason.as_str(),
            self.detail
        ));
        out
    }
}

/// One non-concrete fsym obligation that would need a stronger backend.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsymTrustIrUnknown {
    pub kind: FsymTrustIrDiagnosticKind,
    pub label: String,
    pub module: String,
    pub function: String,
    pub block: u32,
    pub inst_index: usize,
    pub reason: String,
    pub path_guards: Vec<String>,
    pub candidate_expression: Option<String>,
    pub solver_candidate: Option<FsymTrustIrSolverCandidate>,
}

impl FsymTrustIrUnknown {
    /// Render this unknown obligation as a stable warning diagnostic.
    pub fn render(&self, input: Option<&Path>) -> String {
        let mut out = "warning[fsym]: ".to_string();
        if let Some(input) = input {
            out.push_str(&format!("{}: ", input.display()));
        }
        out.push_str(&format!(
            "unknown obligation {} label `{}` in module `{}` function `{}` bb{} inst{}: {}",
            self.kind.as_str(),
            self.label,
            self.module,
            self.function,
            self.block,
            self.inst_index,
            self.reason
        ));
        if let Some(candidate_expression) = &self.candidate_expression {
            out.push_str(&format!("; candidate: {candidate_expression}"));
        }
        if !self.path_guards.is_empty() {
            out.push_str(&format!("; guards: {}", self.path_guards.join(" && ")));
        }
        out
    }
}

/// Structured solver handoff for a bounded fsym unknown.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsymTrustIrSolverCandidate {
    pub path_guards: Vec<SmtExpr>,
    pub obligation: FsymTrustIrSolverObligation,
}

/// Conservative obligation shapes accepted by the bounded fsym escalation path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FsymTrustIrSolverObligation {
    NullDeref {
        ptr: SmtExpr,
        ptr_width: u32,
    },
    Arithmetic {
        kind: ArithUbKind,
        lhs: SmtExpr,
        rhs: Option<SmtExpr>,
        width: u32,
    },
    OutOfBounds {
        byte_offset: SmtExpr,
        object_size_bytes: SmtExpr,
        access_size_bytes: u64,
        width: u32,
    },
    /// The site is UB whenever it is reached: the obligation is that the
    /// path guards are unsatisfiable (an `unreachable` terminator).
    Reachable,
}

/// A reachable obligation the scanner failed to account for.
///
/// This is the fail-closed backstop for the deref-coverage invariant: every
/// reachable obligation site walked by the scanner — a memory access
/// (`Load`/`Store`/`Atomic*`/`AtomicRMW`/`CmpXchg`/`MemCopy`/`MemSet`), a
/// direct call to a bulk-memory symbol or to a callee whose memory effects
/// are unsummarized, and an arithmetic operation with a UB side condition —
/// MUST be discharged by at least one verdict — `Safe` (with a recorded
/// justification), a concrete-UB `Diagnostic`, or an `Unknown`. If a site is
/// walked but no verdict is recorded for it, the obligation was silently
/// dropped — i.e. the scanner would be *failing open*, asserting a safety it
/// never proved. The same error names a block terminator whose successors
/// could not be walked: every obligation in those blocks would be dropped.
/// Rather than let that pass silently, the scanner records this error and
/// callers treat it as fatal (mirroring the opcode `coverage_gate`: an
/// unaccounted obligation is never an implicit pass).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsymCoverageError {
    pub module: String,
    pub function: String,
    pub block: u32,
    pub inst_index: usize,
    /// The memory-access opcode whose obligation was dropped (e.g. "Load").
    pub opcode: &'static str,
    pub detail: String,
}

impl FsymCoverageError {
    /// Render this coverage gap as a stable error diagnostic.
    pub fn render(&self, input: Option<&Path>) -> String {
        let mut out = "error[fsym]: ".to_string();
        if let Some(input) = input {
            out.push_str(&format!("{}: ", input.display()));
        }
        out.push_str(&format!(
            "deref-coverage invariant violated: reachable {} in module `{}` function `{}` bb{} inst{} recorded no verdict (fail-closed): {}",
            self.opcode, self.module, self.function, self.block, self.inst_index, self.detail
        ));
        out
    }
}

/// Scanner output: concrete UB diagnostics plus bounded-scope accounting.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FsymTrustIrReport {
    pub diagnostics: Vec<FsymTrustIrDiagnostic>,
    pub scanned_functions: usize,
    pub scanned_function_names: Vec<String>,
    pub skipped_functions: Vec<FsymTrustIrSkip>,
    pub unknown_obligations: Vec<FsymTrustIrUnknown>,
    /// Fail-closed deref-coverage violations: reachable memory accesses that
    /// were walked but produced no verdict. A non-empty list means the
    /// scanner dropped an obligation and MUST be treated as fatal.
    pub coverage_errors: Vec<FsymCoverageError>,
}

impl FsymTrustIrReport {
    pub fn has_concrete_ub(&self) -> bool {
        !self.diagnostics.is_empty()
    }

    /// True if the deref-coverage invariant was violated for any function.
    ///
    /// A coverage gap is a dropped obligation (the scanner failed open). It is
    /// fatal: callers must reject the module rather than emit code on the
    /// strength of an unproven safety assertion.
    pub fn has_coverage_error(&self) -> bool {
        !self.coverage_errors.is_empty()
    }

    /// The UB classes this report's verdicts are about: a clean function is
    /// clean with respect to the `Checked` ones (`FSYM_TRUST_IR_UB_CLASSES`).
    pub fn ub_classes(&self) -> &'static [FsymUbClass] {
        FSYM_TRUST_IR_UB_CLASSES
    }

    /// The runs this report's verdicts are about: a clean function is free
    /// of the checked UB in every run [`FSYM_RUN_MODEL`] admits, and in no
    /// other run is it claimed to be.
    pub fn run_model(&self) -> FsymRunModel {
        FSYM_RUN_MODEL
    }

    /// One `note[fsym]` line per UB class, stating whether it is checked and
    /// how many of the reference interpreter's UB sites it covers
    /// (`fsym_ub_map`).
    pub fn render_ub_classes(&self) -> Vec<String> {
        let sites = crate::fsym_ub_map::fsym_sites_per_class();
        self.ub_classes()
            .iter()
            .map(|class| {
                let count = sites
                    .iter()
                    .find(|(name, _)| *name == class.name)
                    .map_or(0, |(_, count)| *count);
                match class.status {
                    FsymUbClassStatus::Checked(kind) => format!(
                        "note[fsym]: UB class `{}` checked (kind {}, {count} interpreter UB site(s)): {}",
                        class.name,
                        kind.as_str(),
                        class.detail
                    ),
                    FsymUbClassStatus::NotChecked => format!(
                        "note[fsym]: UB class `{}` not checked ({count} interpreter UB site(s)): {}",
                        class.name, class.detail
                    ),
                }
            })
            .collect()
    }
}

/// Where a tracked allocation lives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ObjectKind {
    /// `Alloca`: freed by the frame, never by `Dealloc`.
    Stack,
    /// `HeapAlloc` of a cell that is not reference-counted (`RustHeap` /
    /// `CMalloc`, trust-ir's `AllocOrigin::is_reference_counted` false):
    /// `Dealloc` of its base frees it.
    Heap,
    /// `HeapAlloc` of a reference-counted cell (`SwiftHeap` / `CleanHeap`,
    /// `AllocOrigin::is_reference_counted` true):
    /// released only by the `Release` that takes its count to zero, so
    /// `Dealloc` of it is undefined behaviour (trust-ir's reference
    /// interpreter, `MemoryState::dealloc`; SPEC "A reference-counted cell is
    /// released by `Release`, never by `Dealloc`").
    RcHeap,
}

/// A tracked allocation: the provenance of a pointer that points into it.
///
/// `id` is an IDENTITY of the allocation site, never a value. The object's
/// address is unknown, so nothing may compare, fold, cast or prune on `id`;
/// it only tells two tracked objects apart and keys the per-path lifetime
/// and initialization state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ObjectRef {
    id: u64,
    kind: ObjectKind,
    /// The alignment (bytes) the object's base is guaranteed: its explicit
    /// alignment, or its type's natural one. `None` when neither is known.
    base_align: Option<u64>,
    /// The object's size in bytes, when it is a constant.
    size_bytes: Option<u64>,
}

/// What the scanner knows about one pointer value (see the module docs).
#[derive(Debug, Clone)]
struct PointerFacts {
    /// The run-time address as an EXACT expression over the scan's free
    /// inputs (`0` for null, a constant, a parameter's variable, plus exact
    /// GEP offsets), or `None` when it is abstract (a tracked object's base
    /// address is unknown). Only this may be compared, cast to an integer or
    /// decide null-ness.
    addr: Option<SmtExpr>,
    /// The tracked allocation the pointer points into, if any.
    object: Option<ObjectRef>,
    /// Byte offset from `object`'s base, when modeled.
    byte_offset: Option<SmtExpr>,
    /// `object`'s size as a 64-bit constant (bounds checks).
    object_size_bytes: Option<SmtExpr>,
    /// The pointer points into a stack object (the interpreter's `Alloca`
    /// never yields null), or was moved from one by a GEP. Never set by a
    /// proof annotation: an annotation is a claim nothing here checks.
    not_null_proven: bool,
    /// `addr` is an address the interpreter can compute for this pointer
    /// (its `address()`: base + offset within the target's address space,
    /// of an allocation the run made): null, a constant, an integer turned
    /// into a pointer (checked when it was), and a GEP of one whose no-wrap
    /// is proven. Not a parameter: a caller's GEP moves an allocation OFFSET
    /// and faults only when that overflows u64, so the pointer it hands over
    /// may lie where base + offset has no address.
    nameable: bool,
}

impl PointerFacts {
    /// A pointer with no tracked provenance whose address, when modeled, is
    /// one the interpreter computes for it.
    fn untracked(addr: Option<SmtExpr>) -> Self {
        Self {
            addr,
            object: None,
            byte_offset: None,
            object_size_bytes: None,
            not_null_proven: false,
            nameable: true,
        }
    }
}

#[derive(Debug, Clone)]
struct ValueFacts {
    ty: Ty,
    expr: Option<SmtExpr>,
    pointer: Option<PointerFacts>,
    /// For a `Ty::Enum` value: the index of its ACTIVE variant, when the
    /// scanner knows it (built by `Const` / `MakeAggregate` on this path,
    /// possibly through `Copy` or `InsertField`). A payload lane of any other
    /// variant is UB to extract or insert.
    variant: Option<u32>,
    /// For a float made by `SIToFP` / `UIToFP` (possibly through `Copy`):
    /// the integer it was converted from. Its value is then bounded by that
    /// integer's range, and never NaN (`check_float_to_int`).
    int_as_float: Option<IntAsFloat>,
    /// Exact flat runtime capture values, copied by value. This does not model
    /// invocation or retain a callable-target fact. Missing facts stay unknown.
    closure_captures: Option<Vec<ValueFacts>>,
}

/// A float converted from an integer of `bits` bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct IntAsFloat {
    signed: bool,
    bits: u32,
    /// Every value of the integer is exactly representable (`bits` fits the
    /// float's significand), so the conversion does not round.
    exact: bool,
}

type VerdictEvidence = (Option<String>, Option<FsymTrustIrSolverObligation>);

/// Operands of one bulk memory access: a `MemCopy` / `MemSet` instruction,
/// or a direct call to a C / LLVM bulk-memory symbol (see
/// `bulk_memory_symbol`).
#[derive(Debug, Clone, Copy)]
struct BulkMemoryOp {
    /// Names the access in messages: `MemCopy`, `MemSet`, or the callee
    /// symbol of a bulk-memory call.
    opcode: &'static str,
    dst: ValueId,
    /// The source range of a copy; `None` for a set.
    src: Option<ValueId>,
    bytes: ValueId,
    /// True for a `MemCopy` without `overlap`, or a call to a `memcpy`
    /// symbol (`memcpy` semantics), where overlapping ranges are UB.
    overlap_is_ub: bool,
}

/// The byte count of a bulk memory instruction, as far as the scanner models
/// it.
#[derive(Debug, Clone)]
enum BulkLen {
    /// Concretely zero: a defined no-op, even through a null or dangling
    /// pointer.
    Zero,
    /// A concrete nonzero count.
    Concrete(u64),
    /// A modeled, non-constant bit-vector count.
    Symbolic(SmtExpr),
    /// No modeled value (loaded from memory, a call result, ...).
    Unmodeled,
}

/// Facts about the whole module every function scan of it shares, each
/// computed at most once: per `scan_module`, per `scan_function_in_module`
/// call, or — inside a [`with_fsym_module_scope`] of the module — once for
/// every function scan of it.
#[derive(Debug, Default)]
struct ModuleFacts {
    /// [`budget_premise_violation`], once a placement verdict asks for it.
    budget_premise: OnceLock<Option<String>>,
    /// [`module_unwritten_lane`], once a function scan asks for it.
    unwritten_lane: OnceLock<Option<String>>,
    storage_surface: OnceLock<bool>,
    abi_contract_surface: OnceLock<Option<String>>,
    nominal_item_surface: OnceLock<bool>,
}

/// Legacy ABI entry/return promises are outside the bounded body model,
/// including those on an unused declaration. Typed signature descriptors
/// retain the separate existing module-wide boundary below.
fn module_abi_contract_surface(module: &Module) -> Option<String> {
    module.functions.iter().find_map(|function| {
        (function.attrs.params.iter().any(|attrs| !attrs.is_empty())
            || !function.attrs.ret.is_empty())
        .then(|| {
            format!(
                "legacy ABI parameter/result contracts on {} have no complete bounded fsym model",
                function.name
            )
        })
    })
}

/// Where `module` spells a trust-ir v49 unwritten aggregate lane
/// (`Constant::Uninit`): an `Inst::Const`, a `Switch` case or a global
/// initializer of ANY function or global, scanned or not. No instruction
/// yields an unwritten lane otherwise, and memory records one only when a
/// value carrying one is stored, so a module that spells none has none in
/// any run fsym models. fsym models no unwritten lane (the reference
/// interpreter's reads of one are UB that no verdict here is owed for), so
/// it scans no function of a module that spells one. `None` when it spells
/// none.
fn module_unwritten_lane(module: &Module) -> Option<String> {
    let carries = |constant: &Constant| {
        constant
            .try_visit_constants(|nested| {
                if matches!(nested, Constant::Uninit) {
                    std::ops::ControlFlow::Break(())
                } else {
                    std::ops::ControlFlow::Continue(())
                }
            })
            .is_break()
    };
    let refusal = |location: String| {
        Some(format!(
            "the module spells a trust-ir v49 unwritten aggregate lane (Constant::Uninit) at \
             {location}; fsym models no unwritten lane, so no function of the module is scanned"
        ))
    };
    for global in &module.globals {
        if global.initializer.as_ref().is_some_and(carries) {
            return refusal(format!("global `{}`", global.name));
        }
    }
    for function in &module.functions {
        for block in &function.blocks {
            for node in &block.body {
                let spelled = match &node.inst {
                    Inst::Const { value, .. } => carries(value),
                    Inst::Switch { cases, .. } => cases.iter().any(|case| carries(&case.value)),
                    _ => false,
                };
                if spelled {
                    return refusal(format!(
                        "function `{}` bb{}",
                        function.name,
                        block.id.index()
                    ));
                }
            }
        }
    }
    None
}

/// One open module scope: the module's address (and its function table's, a
/// defensive check), how many scopes of it are open, and the facts they
/// share.
struct OpenModuleScope {
    module: usize,
    functions: (usize, usize),
    depth: usize,
    facts: Arc<ModuleFacts>,
}

/// The module scopes open in this process: each exactly while a
/// [`with_fsym_module_scope`] call of its module runs.
static OPEN_MODULE_SCOPES: Mutex<Vec<OpenModuleScope>> = Mutex::new(Vec::new());

fn open_module_scopes() -> std::sync::MutexGuard<'static, Vec<OpenModuleScope>> {
    OPEN_MODULE_SCOPES
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

fn module_scope_key(module: &Module) -> (usize, (usize, usize)) {
    (
        std::ptr::from_ref(module) as usize,
        (module.functions.as_ptr() as usize, module.functions.len()),
    )
}

/// Run `scans` with `module`'s facts shared: every [`scan_function_in_module`]
/// and [`scan_module`] of `module` made while it runs — on this thread or
/// another — decides the module-level facts (the BUDGET premise, a pass over
/// every function of the module) once for all of them, not once per call. A
/// compiler scanning a module function by function runs its loop in here.
///
/// The facts are shared exactly for the duration of this call, which borrows
/// the module: it cannot change, move or be dropped while they are. There is
/// no guard a caller could leak (`mem::forget`) to keep them past an edit of
/// the module in place — the scope opened and closed here is private, and
/// closes on return and on unwind. Outside it every call decides the facts
/// afresh: always correct, only slower.
pub fn with_fsym_module_scope<R>(module: &Module, scans: impl FnOnce() -> R) -> R {
    let _open = OpenScopeGuard::enter(module);
    scans()
}

/// Registers `module`'s scope for the life of one [`with_fsym_module_scope`]
/// call. Private: nothing outside that call can hold (or leak) one.
struct OpenScopeGuard {
    key: (usize, (usize, usize)),
}

impl OpenScopeGuard {
    fn enter(module: &Module) -> Self {
        let (address, functions) = module_scope_key(module);
        let mut scopes = open_module_scopes();
        match scopes.iter_mut().find(|scope| scope.module == address) {
            Some(scope) => {
                // The borrow of an open scope pins the module: nothing at
                // this address can be another module while it is open.
                debug_assert_eq!(scope.functions, functions);
                scope.depth += 1;
            }
            None => scopes.push(OpenModuleScope {
                module: address,
                functions,
                depth: 1,
                facts: Arc::new(ModuleFacts::default()),
            }),
        }
        Self {
            key: (address, functions),
        }
    }
}

impl Drop for OpenScopeGuard {
    fn drop(&mut self) {
        let mut scopes = open_module_scopes();
        if let Some(index) = scopes.iter().position(|scope| scope.module == self.key.0) {
            scopes[index].depth -= 1;
            if scopes[index].depth == 0 {
                scopes.swap_remove(index);
            }
        }
    }
}

/// The facts the scans of `module` share: its open scope's, else fresh ones.
fn module_facts(module: &Module) -> Arc<ModuleFacts> {
    let (address, functions) = module_scope_key(module);
    open_module_scopes()
        .iter()
        .find(|scope| scope.module == address && scope.functions == functions)
        .map_or_else(
            || Arc::new(ModuleFacts::default()),
            |scope| Arc::clone(&scope.facts),
        )
}

/// Why a placement of `ty` whose footprint is `footprint` bytes (`None`:
/// not computable, or past 2^64) is not decided: it reaches
/// [`FSYM_TRUST_IR_MAX_MODELED_FOOTPRINT`], so whether the address space
/// still holds it depends on placements the scan does not bound. `None` when
/// it is below.
fn footprint_past_the_model(ty: &Ty, footprint: Option<u64>) -> Option<String> {
    match footprint {
        Some(bytes) if bytes < FSYM_TRUST_IR_MAX_MODELED_FOOTPRINT => None,
        Some(bytes) => Some(format!(
            "this placement of {ty:?} is {bytes} bytes, at least the {FSYM_TRUST_IR_MAX_MODELED_FOOTPRINT}-byte footprint fsym decides placements below: whether the address space still holds it (else OutOfMemory) depends on placements the scan does not bound, so its verdict is not taken from the model"
        )),
        None => Some(format!(
            "the footprint of this placement of {ty:?} is past 2^64 or not computable: whether the address space holds it is not decided"
        )),
    }
}

/// Where the module may break the BUDGET premise (see the module docs): the
/// first instruction of any function of `module` — scanned or not — that
/// may place an allocation at an alignment past
/// [`FSYM_TRUST_IR_MAX_MODELED_ALIGN`], or at one fsym cannot lay out: an
/// `Alloca` / `HeapAlloc` (`align`, else its type's natural alignment), a
/// `SeqMap` (an element cell at the element's natural alignment), an
/// instruction materializing a global (placed at `max(natural, declared,
/// 16)`, with every global its initializers address) — or that places
/// allocations no step pays for, so the run model's fuel does not bound
/// them: a `SeqMap` through a function with no body (a host model serves
/// the call per cell). `None` when every run of the module in the model
/// places every allocation within it.
pub(crate) fn budget_premise_violation(module: &Module) -> Option<String> {
    let past =
        |align: Option<u64>| align.is_none_or(|align| align > FSYM_TRUST_IR_MAX_MODELED_ALIGN);
    let describe = |align: Option<u64>| {
        align.map_or("an alignment fsym cannot lay out".to_string(), |align| {
            format!("alignment {align}")
        })
    };
    for function in &module.functions {
        for block in &function.blocks {
            for (index, node) in block.body.iter().enumerate() {
                let placed = match &node.inst {
                    Inst::Alloca { ty, align, .. } | Inst::HeapAlloc { ty, align, .. } => {
                        let placement = allocation_align(module, ty, *align);
                        past(placement).then(|| {
                            format!("places an allocation of {ty:?} at {}", describe(placement))
                        })
                    }
                    Inst::SeqMap { fwd, .. }
                        if module
                            .function_by_id(*fwd)
                            .is_none_or(Function::is_declaration) =>
                    {
                        Some(
                            "maps a sequence through a function with no body: a host model serves each call with no step, so the element cells it places are not bounded by the run model's fuel"
                                .to_string(),
                        )
                    }
                    Inst::SeqMap { fwd, .. } => {
                        let element = module
                            .function_by_id(*fwd)
                            .and_then(|callee| module.func_type(callee.ty))
                            .and_then(|sig| match sig.params.as_slice() {
                                [Ty::RefMut(element)] => Some((**element).clone()),
                                _ => None,
                            });
                        let placement = element
                            .as_ref()
                            .and_then(|element| allocation_align(module, element, None));
                        past(placement).then(|| {
                            format!("places a `SeqMap` element cell at {}", describe(placement))
                        })
                    }
                    inst if materializes_global(inst) => materialized_globals(module, inst)
                        .into_iter()
                        .find_map(|index| {
                            let Some(global) = module.globals.get(index) else {
                                return Some(format!(
                                    "materializes global #{index}, which does not resolve"
                                ));
                            };
                            let placement = global_align(module, global);
                            past(placement).then(|| {
                                format!(
                                    "materializes global `{}` at {}",
                                    global.name,
                                    describe(placement)
                                )
                            })
                        }),
                    _ => None,
                };
                if let Some(placed) = placed {
                    return Some(format!(
                        "`{}` bb{}:{index} {placed}",
                        function.name,
                        block.id.index()
                    ));
                }
            }
        }
    }
    None
}

/// What a scalar access does with the bytes it touches.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MemoryAccess {
    Read,
    Write,
    /// `AtomicRMW` / `CmpXchg`: reads, then writes.
    ReadWrite,
}

/// Why an access through `pointer` (which has no tracked object) cannot be
/// checked against an object.
fn untracked_reason(pointer: &PointerFacts) -> &'static str {
    match &pointer.addr {
        Some(addr) if addr.free_vars().is_empty() => {
            "the pointer is a constant or integer-derived address with no tracked provenance; the reference interpreter faults a dereference through an address naming no allocation, and fsym cannot tell which allocation (if any) it names"
        }
        Some(_) => {
            "the pointer has no tracked provenance (a parameter, or an address computed from inputs): the object it points into is not tracked"
        }
        None => "the pointer has no tracked provenance: the object it points into is not tracked",
    }
}

/// The pointer's run-time address when it is an exact CONSTANT (null, a
/// constant address, `inttoptr` of a constant).
fn exact_constant_address(pointer: &PointerFacts) -> Option<u64> {
    pointer.addr.as_ref().and_then(eval_concrete_u64)
}

/// The target facts the scanner models a module at.
///
/// Every size, offset, stride and alignment the scanner reasons with is the
/// reference interpreter's (`fsym_layout::FsymLayout`, a port of its layout
/// functions) at the module's pointer width — the one layout authority the
/// UB it owes verdicts for is defined by. There is no other.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScanTarget {
    /// The width, in bits, of `Usize` / `Isize` values:
    /// `target_info.pointer_size * 8`. `None` for a target-free module; a
    /// function with a `Usize` / `Isize` value is then refused by name
    /// (`FsymTrustIrSkipReason::PointerWidth`) before it is walked.
    pointer_bits: Option<u32>,
}

impl ScanTarget {
    /// Pointers narrower than 64 bits (see the module docs): the interpreter
    /// keeps every placement inside the address space (OutOfMemory past it),
    /// so no placement overflows whatever its alignment, and a non-empty
    /// object may end exactly at `2^pointer_bits`, where a pointer one past
    /// it has no address.
    fn end_may_be_unnameable(self) -> bool {
        self.pointer_bits.is_some_and(|bits| bits < 64)
    }
}

/// Whether a pointer `offset` bytes into an object of `size` bytes has an
/// address the target can name, on every placement of the object: its base
/// and every byte in it do; one past its end does only where the target's
/// address space cannot end there (`ScanTarget::end_may_be_unnameable`).
fn offset_is_nameable(target: ScanTarget, offset: u128, size: u64) -> bool {
    offset < u128::from(size)
        || offset == 0
        || (offset == u128::from(size) && !target.end_may_be_unnameable())
}

/// The target a module is scanned at, or the named reason no function of it
/// can be: the reference interpreter executes (and lays out) only a
/// target-free module or a little-endian canonical-scalar-table target with
/// 32- or 64-bit pointers (`require_reference_execution_layout`), and fsym
/// has no layout but the interpreter's.
fn scan_target(module: &Module) -> Result<ScanTarget, String> {
    FsymLayout::new(module)
        .reference_execution()
        .map_err(|detail| format!("fsym uses the reference interpreter's layout only: {detail}"))?;
    let Some(target) = &module.target_info else {
        return Ok(ScanTarget { pointer_bits: None });
    };
    match target.pointer_size {
        8 => Ok(ScanTarget {
            pointer_bits: Some(64),
        }),
        4 => Ok(ScanTarget {
            pointer_bits: Some(32),
        }),
        other => Err(format!(
            "module target `{}` pins {other}-byte pointers; fsym models Usize/Isize only at 8- or 4-byte pointers",
            target.triple
        )),
    }
}

#[derive(Debug, Clone)]
struct FunctionScan<'a> {
    module: &'a Module,
    function: &'a Function,
    block: &'a Block,
    target: ScanTarget,
    values: HashMap<ValueId, ValueFacts>,
    ctx: PathContext,
    /// The first branch on this path whose condition (or switch selector) had
    /// no modeled value. Both arms of such a branch are walked with no path
    /// fact added, so nothing on the path after it is known to be reachable:
    /// `record_verdict` reports a concrete-UB verdict there as an Unknown
    /// (UB if reached) and withholds solver candidates, whose models could
    /// only pick the branch outcome as if it were a free input.
    unmodeled_branch: Option<String>,
    uaf_events: Vec<UafEvent>,
    uaf_reported: bool,
    /// Per tracked object (by id): which bytes are proven initialized on this
    /// path. Objects larger than `FSYM_TRUST_IR_MAX_INIT_TRACKED_BYTES`, or of
    /// non-constant size, have no entry (every load from them is Unknown).
    init: HashMap<u64, Vec<bool>>,
    /// Tracked objects whose address escaped (stored as a value, passed to a
    /// call, cast to an integer): any later call may reach them.
    escaped: HashSet<u64>,
    /// Tracked objects a call may have freed or overwritten on this path,
    /// with the call that did: their later lifetime and contents are Unknown.
    havocked: HashMap<u64, String>,
    /// The first `Dealloc` on this path of a pointer with no tracked
    /// provenance: it may have freed any object whose address escaped, so
    /// every later lifetime verdict is Unknown.
    untracked_free: Option<String>,
    /// The first call on this path: a later `unreachable` is reached only if
    /// it returns.
    passed_call: Option<String>,
    /// The first `Borrow` / `BorrowMut` on this path: trust-ir's permission
    /// model forbids freeing while borrowed, which the scanner does not track.
    borrow_seen: Option<String>,
    /// Bodied callees of the scanned function that the scanner refuses to
    /// scan, with the refusal: a pointer handed to one is unsummarized.
    skipped_callees: Rc<HashMap<FuncId, String>>,
    /// Facts about the whole module, shared by every scan of it.
    module_facts: Arc<ModuleFacts>,
    diagnostics: Vec<FsymTrustIrDiagnostic>,
    unknown_obligations: Vec<FsymTrustIrUnknown>,
    /// Deref-coverage accounting for the block currently being walked: the
    /// `(inst_index, kind)` pairs at which `record_verdict` produced a
    /// verdict. After a block is walked, every obligation `obligation_kinds`
    /// lists for a reachable site MUST appear here, or it was dropped
    /// (fail-closed — see `FsymCoverageError`).
    covered: HashSet<(usize, FsymTrustIrDiagnosticKind)>,
    coverage_errors: Vec<FsymCoverageError>,
    /// Test-only fault injection: when true, `check_null` reproduces the
    /// historical fail-open behaviour (silent early return, no verdict
    /// recorded) so the deref-coverage invariant can be exercised against a
    /// deliberately dropped obligation. Never set outside tests.
    #[cfg(test)]
    force_drop_deref: bool,
}

/// Scan a trust_ir module for concrete UB in bounded straight-line functions.
pub fn scan_module(module: &Module) -> FsymTrustIrReport {
    let mut report = FsymTrustIrReport::default();
    let target = scan_target(module);
    let facts = module_facts(module);
    for function in &module.functions {
        scan_one_function(module, function, &target, &facts, &mut report);
    }
    report
}

/// Scan ONE function in the context of the module that contains it.
///
/// The module supplies what the function's own body cannot: the declared
/// name, linkage and signature of every direct callee (a call to `memset`
/// is a bulk memory access; a call to an unknown external taking a pointer
/// is an unsummarized memory effect), the type tables, and the target
/// pointer width. Scanning a function in a module stripped of its callees
/// would make every call unresolved. Module-level facts (the BUDGET premise)
/// are decided per call, or once for all calls made inside a
/// [`with_fsym_module_scope`] of the module.
pub fn scan_function_in_module(module: &Module, function: &Function) -> FsymTrustIrReport {
    let mut report = FsymTrustIrReport::default();
    let facts = module_facts(module);
    scan_one_function(module, function, &scan_target(module), &facts, &mut report);
    report
}

fn scan_one_function(
    module: &Module,
    function: &Function,
    target: &Result<ScanTarget, String>,
    facts: &Arc<ModuleFacts>,
    report: &mut FsymTrustIrReport,
) {
    if let Some(detail) = facts
        .abi_contract_surface
        .get_or_init(|| module_abi_contract_surface(module))
    {
        report.skipped_functions.push(FsymTrustIrSkip {
            function: function.name.clone(),
            reason: FsymTrustIrSkipReason::UnsupportedInstruction,
            detail: detail.clone(),
        });
        return;
    }
    if let Some(detail) = facts
        .unwritten_lane
        .get_or_init(|| module_unwritten_lane(module))
    {
        report.skipped_functions.push(FsymTrustIrSkip {
            function: function.name.clone(),
            reason: FsymTrustIrSkipReason::UnsupportedInstruction,
            detail: detail.clone(),
        });
        return;
    }
    // The public scanner also accepts a supplied body outside the module's
    // function table. Its actual spelled types cannot borrow cached absence
    // established for a different body in that table.
    let supplied_nominal = !module
        .function_by_id(function.id)
        .is_some_and(|member| std::ptr::eq(member, function))
        && {
            let mut found = false;
            for block in &function.blocks {
                for (_, ty) in &block.params {
                    ty.visit_types(|ty| found |= matches!(ty, Ty::FnItem(_)));
                }
                for node in &block.body {
                    node.inst
                        .visit_types(|ty| found |= matches!(ty, Ty::FnItem(_)));
                }
            }
            found
        };
    if supplied_nominal
        || *facts.nominal_item_surface.get_or_init(|| {
            let mut found = false;
            module.visit_types(|ty| found |= matches!(ty, Ty::FnItem(_)));
            found
        })
    {
        report.skipped_functions.push(FsymTrustIrSkip {
            function: function.name.clone(),
            reason: FsymTrustIrSkipReason::UnsupportedInstruction,
            detail: "FnItem nominal identity has no complete bounded fsym value model".into(),
        });
        return;
    }
    if *facts.storage_surface.get_or_init(|| {
        let mut found = false;
        module.visit_types(|ty| found |= matches!(ty, Ty::Storage(_)));
        found
    }) {
        report.skipped_functions.push(FsymTrustIrSkip {
            function: function.name.clone(),
            reason: FsymTrustIrSkipReason::UnsupportedInstruction,
            detail: "Storage geometry has no complete bounded fsym typed-value/global-policy model"
                .into(),
        });
        return;
    }
    let target = match validate_function_scope(module, function, target) {
        Ok(target) => target,
        Err(skip) => {
            report.skipped_functions.push(FsymTrustIrSkip {
                function: function.name.clone(),
                reason: skip.reason,
                detail: skip.detail,
            });
            return;
        }
    };

    report.scanned_functions += 1;
    report.scanned_function_names.push(function.name.clone());
    let skipped = Rc::new(skipped_direct_callees(module, function, target));
    let scan = scan_function(module, function, target, skipped, Arc::clone(facts));
    report.diagnostics.extend(scan.diagnostics);
    report.unknown_obligations.extend(scan.unknown_obligations);
    report.coverage_errors.extend(scan.coverage_errors);
}

/// The bodied, module-bound direct callees of `function` that the scanner
/// refuses to scan (`validate_function_scope`), each with its refusal. Their
/// accesses through a pointer the caller hands them are checked nowhere, so
/// such a call is unsummarized (`visit_call`). Validating a callee never
/// consults this table, so mutual recursion cannot loop.
fn skipped_direct_callees(
    module: &Module,
    function: &Function,
    target: ScanTarget,
) -> HashMap<FuncId, String> {
    let target = Ok(target);
    let mut skipped = HashMap::new();
    let mut seen = HashSet::new();
    for node in function.blocks.iter().flat_map(|block| &block.body) {
        let Inst::Call { callee, .. } = &node.inst else {
            continue;
        };
        if !seen.insert(*callee) {
            continue;
        }
        let Some(callee_function) = module.function_by_id(*callee) else {
            continue;
        };
        if !callee_binds_to_module_body(callee_function) {
            continue;
        }
        if let Err(skip) = validate_function_scope(module, callee_function, &target) {
            skipped.insert(
                *callee,
                format!("{} ({})", skip.reason.as_str(), skip.detail),
            );
        }
    }
    skipped
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FunctionSkip {
    reason: FsymTrustIrSkipReason,
    detail: String,
}

impl FunctionSkip {
    fn new(reason: FsymTrustIrSkipReason, detail: impl Into<String>) -> Self {
        Self {
            reason,
            detail: detail.into(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CfgEdge {
    source: BlockId,
    target: BlockId,
}

/// The interpreter checks Char at every SSA binding, not just at a use.
/// Inspect ALL blocks and declared result lanes without the lossy zip in
/// typed_values(): unresolved/mismatched result metadata cannot hide a binding.
fn validate_char_binding_scope(module: &Module, function: &Function) -> Result<(), FunctionSkip> {
    // Entry transport validates stored Char lanes recursively before executing
    // instructions. Use the exact shared by-value predicate; opaque addresses
    // stop the walk, while unresolved/cyclic declarations fail closed.
    let layouts = module.layout_table();
    if module.func_type(function.ty).is_some_and(|signature| {
        signature
            .params
            .iter()
            .any(|ty| layouts.type_contains_char_by_value(ty))
    }) {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::UnsupportedInstruction,
            FSYM_CHAR_BINDING_REFUSAL,
        ));
    }
    for block in &function.blocks {
        if block.params.iter().any(|(_, ty)| *ty == Ty::Char) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::UnsupportedInstruction,
                FSYM_CHAR_BINDING_REFUSAL,
            ));
        }
        for (index, node) in block.body.iter().enumerate() {
            let result_types = node.result_tys(module);
            if result_types.contains(&Ty::Char) {
                return Err(FunctionSkip::new(
                    FsymTrustIrSkipReason::UnsupportedInstruction,
                    FSYM_CHAR_BINDING_REFUSAL,
                ));
            }
            if result_types.len() != node.results.len() {
                return Err(FunctionSkip::new(
                    FsymTrustIrSkipReason::MalformedCfg,
                    format!(
                        "bb{} inst{index}: result typing unresolved or arity mismatch; cannot establish absence of Char bindings",
                        block.id.index()
                    ),
                ));
            }
        }
    }
    Ok(())
}

fn validate_function_scope(
    module: &Module,
    function: &Function,
    target: &Result<ScanTarget, String>,
) -> Result<ScanTarget, FunctionSkip> {
    if function.blocks.is_empty() {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::MalformedCfg,
            "function has no blocks",
        ));
    }

    let Some(_signature) = module.func_type(function.ty) else {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::MalformedCfg,
            "function signature is missing",
        ));
    };
    if module
        .func_types
        .iter()
        .any(|signature| signature.abi.is_some())
    {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::UnsupportedInstruction,
            "the module contains a typed signature ABI; its transport and provenance can affect callers and are outside bounded fsym",
        ));
    }

    let target = match target {
        Ok(target) => *target,
        Err(detail) => {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::PointerWidth,
                detail.clone(),
            ));
        }
    };
    if target.pointer_bits.is_none()
        && let Some(detail) = pointer_width_value_detail(module, function)
    {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::PointerWidth,
            format!(
                "{detail}, but the module has no target_info: its width (target_info.pointer_size) is not pinned"
            ),
        ));
    }

    if function.blocks.len() > FSYM_TRUST_IR_MAX_BLOCKS {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::TooLarge,
            format!(
                "function has {} block(s), over fsym bound {}",
                function.blocks.len(),
                FSYM_TRUST_IR_MAX_BLOCKS
            ),
        ));
    }

    if function_block(function, function.entry).is_none() {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::MalformedCfg,
            "entry block is missing",
        ));
    }

    let body_len: usize = function.blocks.iter().map(|block| block.body.len()).sum();
    if body_len > FSYM_TRUST_IR_MAX_STRAIGHT_LINE_INSTRUCTIONS {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::TooLarge,
            format!(
                "function body has {body_len} instruction(s), over fsym bound {FSYM_TRUST_IR_MAX_STRAIGHT_LINE_INSTRUCTIONS}"
            ),
        ));
    }

    validate_char_binding_scope(module, function)?;

    for block in &function.blocks {
        let Some((last, prefix)) = block.body.split_last() else {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::MalformedCfg,
                format!("bb{} has no terminator", block.id.index()),
            ));
        };
        if prefix.iter().any(InstrNode::is_terminator) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::MalformedCfg,
                format!(
                    "bb{} has a terminator before the end of the block",
                    block.id.index()
                ),
            ));
        }
        for (inst_index, node) in prefix.iter().enumerate() {
            validate_supported_nonterminator(module, block.id, inst_index, node)?;
        }
        // v54 (amendment P): the sited check with an unwind edge is refused
        // by its own name before the UB map names one of the UBs it raises;
        // so are the v55 / v56 unwinding twins of a drop and an indirect call.
        let unwinding_twin = match &last.inst {
            Inst::AssertInvoke { .. } => Some(
                "AssertInvoke (a v54 sited check with an unwind edge) requires panic-entry and \
                 host-unwind semantics; fsym models neither",
            ),
            Inst::DropInvoke { .. } => Some(
                "DropInvoke (a v55 drop with an unwind edge) runs the type's drop glue and \
                 requires host-unwind semantics; fsym models no destructor and no unwinding",
            ),
            Inst::InvokeIndirect { .. } => Some(
                "InvokeIndirect (a v56 indirect call with an unwind edge) requires a callee \
                 summary and host-unwind semantics; fsym models neither",
            ),
            _ => None,
        };
        if let Some(detail) = unwinding_twin {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::UnsupportedTerminator,
                format!("bb{} terminator unsupported: {detail}", block.id.index()),
            ));
        }
        if let Some(detail) = fsym_map_refusal(module, &last.inst) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::UnsupportedTerminator,
                format!("bb{} terminator unsupported: {detail}", block.id.index()),
            ));
        }
        match &last.inst {
            Inst::Br { target, args } => {
                validate_edge_args(function, block.id, *target, args)?;
            }
            Inst::CondBr {
                then_target,
                then_args,
                else_target,
                else_args,
                ..
            } => {
                validate_edge_args(function, block.id, *then_target, then_args)?;
                validate_edge_args(function, block.id, *else_target, else_args)?;
            }
            Inst::Return { .. } | Inst::Unreachable => {}
            Inst::Switch {
                value,
                default,
                default_args,
                cases,
                ..
            } => {
                validate_switch_terminator(
                    module,
                    function,
                    block.id,
                    *value,
                    *default,
                    default_args,
                    cases,
                )?;
            }
            _ => {
                return Err(FunctionSkip::new(
                    FsymTrustIrSkipReason::UnsupportedTerminator,
                    format!("bb{} does not end in a terminator", block.id.index()),
                ));
            }
        }
    }

    let backedges = cfg_backedges(function);
    match backedges.as_slice() {
        [] => {}
        [backedge] => validate_bounded_loop_scope(module, function, target, *backedge)?,
        _ => {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "control-flow graph contains {} backedge(s); bounded fsym only supports one static backedge",
                    backedges.len()
                ),
            ));
        }
    }

    Ok(target)
}

/// Names the first value of `function` whose modeled width is the target
/// pointer width (`Usize` / `Isize`, alone or as a vector lane), if any.
fn pointer_width_value_detail(module: &Module, function: &Function) -> Option<String> {
    fn mentions_pointer_width_int(ty: &Ty) -> bool {
        match ty {
            Ty::Usize | Ty::Isize => true,
            Ty::Vector(element, _) => mentions_pointer_width_int(element),
            Ty::Tuple(elements) => elements.iter().any(mentions_pointer_width_int),
            _ => false,
        }
    }
    function
        .typed_values(module)
        .into_iter()
        .find(|metadata| mentions_pointer_width_int(&metadata.ty))
        .map(|metadata| {
            format!(
                "value v{} has pointer-width type {:?}",
                metadata.value.index(),
                metadata.ty
            )
        })
}

fn validate_supported_nonterminator(
    module: &Module,
    block: BlockId,
    inst_index: usize,
    node: &InstrNode,
) -> Result<(), FunctionSkip> {
    // Refused by name; able to raise a UB fsym owes no verdict for (the
    // interpreter-derived UB map, `fsym_ub_map`); or laying out a type the
    // interpreter's layout (`fsym_layout`) has no layout for.
    let Some(detail) = unsupported_nonterminator_detail(module, &node.inst)
        .or_else(|| fsym_map_refusal(module, &node.inst))
        .or_else(|| layout_refusal(module, &node.inst))
    else {
        return Ok(());
    };

    Err(FunctionSkip::new(
        FsymTrustIrSkipReason::UnsupportedInstruction,
        format!(
            "bb{} inst{} unsupported: {detail}",
            block.index(),
            inst_index
        ),
    ))
}

/// The layout refusal of `inst`, if any: an instruction whose execution lays
/// out a type — an allocation's element, an access's value, a GEP's stride —
/// that the bounded reference-layout port (`fsym_layout`, the only one fsym
/// reasons with) cannot lay out. Some forms are also interpreter type errors;
/// newer storage-profile forms have interpreter semantics outside this port.
/// Both are refused by name rather than assigned a guessed size or layout.
pub(crate) fn layout_refusal(module: &Module, inst: &Inst) -> Option<String> {
    let ty = match inst {
        Inst::Alloca { ty, .. }
        | Inst::HeapAlloc { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::Store { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicStore { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::CmpXchg { ty, .. } => ty,
        Inst::GEP { pointee_ty, .. } => pointee_ty,
        _ => return None,
    };
    let layout = FsymLayout::new(module);
    let detail = layout.size(ty).and_then(|_| layout.align(ty)).err()?;
    Some(format!(
        "{} lays out {ty:?}, which has no reference-interpreter layout: {detail}",
        crate::fsym_ub_map::fsym_inst_variant_name(inst)
    ))
}

/// Construction is a pure value operation in the reference semantics. Only
/// flat scalar/thin-pointer captures are modeled; calls remain a separate,
/// refused instruction. Check the same spread signature as eval_make_closure.
fn closure_construction_refusal(
    module: &Module,
    ty: trust_ir::ClosureTyId,
    func: FuncId,
    count: usize,
) -> Option<String> {
    let invalid = |detail| Some(format!("MakeClosure: {detail}"));
    let Some(closure) = module.closure_type(ty) else {
        return invalid("undefined closure type");
    };
    if closure.captures.iter().any(|ty| {
        !(ty.is_integer() || ty.is_float() || matches!(ty, Ty::Bool | Ty::Ptr | Ty::Unit))
    }) {
        return invalid("only flat scalar/thin-pointer captures are modeled (no Char or handles)");
    }
    if closure.captures.len() != count {
        return invalid("capture count disagrees with the declared closure type");
    }
    let Some(apparent) = module.func_type(closure.func) else {
        return invalid("undefined apparent signature");
    };
    let Some(target) = module.function_by_id(func) else {
        return invalid("undefined target function");
    };
    let Some(physical) = module.func_type(target.ty) else {
        return invalid("undefined target signature");
    };
    let params: Vec<_> = closure
        .captures
        .iter()
        .chain(&apparent.params)
        .cloned()
        .collect();
    if apparent.is_vararg
        || physical.is_vararg
        || physical.params != params
        || physical.returns != apparent.returns
        || physical.abi != apparent.abi
    {
        return invalid(
            "target signature must be captures followed by apparent parameters, with apparent returns and ABI",
        );
    }
    None
}

/// The bounded scanner's admission gate for one non-terminator instruction:
/// `Some(detail)` refuses the whole function (`UnsupportedInstruction`),
/// `None` admits it — subject also to the interpreter-derived UB map
/// (`fsym_ub_map::fsym_map_refusal`, consulted by
/// `validate_supported_nonterminator`): an instruction that can raise a UB
/// fsym owes no verdict for is refused by that UB's name.
///
/// EXHAUSTIVE over `trust_ir::Inst` on purpose — no wildcard. A variant added
/// to trust-ir must fail to compile here until someone decides whether the
/// scanner models it; a `_ => None` default admitted `MemCopy` / `MemSet`
/// (trust-ir WS3.20) as if they touched no memory, so a null or overflowing
/// bulk write scanned clean. Every admitted variant is either checked by
/// `visit_node` (each obligation it carries owes a verdict, enforced by
/// `reachable_obligation_sites`) or performs no memory access the scanner
/// is responsible for; see the arms below.
/// Whether `value` is, or holds at any depth, a trust-ir v70
/// `Constant::TensorBlob`.
fn carries_tensor_blob(value: &Constant) -> bool {
    value
        .try_visit_constants(|nested| {
            if matches!(nested, Constant::TensorBlob { .. }) {
                std::ops::ControlFlow::Break(())
            } else {
                std::ops::ControlFlow::Continue(())
            }
        })
        .is_break()
}

/// Whether the in-memory representation of `ty` can contain an enum value.
///
/// The reference interpreter reconstructs an enum's active variant from its
/// byte image on a load (and on a layout-sensitive cast). Bounded fsym has no
/// discriminant-validity obligation, so such an instruction must be refused
/// before it can be scanned. Pointers stop the walk: their pointee's bytes are
/// not part of the pointer value. Missing, cyclic, or unexpectedly deep type
/// table paths fail closed.
fn type_may_contain_enum_by_value(module: &Module, ty: &Ty) -> bool {
    fn walk(module: &Module, ty: &Ty, depth: usize) -> bool {
        if depth > 64 {
            return true;
        }
        match ty {
            Ty::Enum(_) => true,
            Ty::Vector(element, _) | Ty::Tensor(element, _) => walk(module, element, depth + 1),
            Ty::Tuple(elements) => elements
                .iter()
                .any(|element| walk(module, element, depth + 1)),
            Ty::Array(element, _)
            | Ty::Set(element, _)
            | Ty::Sequence(element)
            | Ty::Refine(element, _) => module
                .ty(*element)
                .is_none_or(|element| walk(module, element, depth + 1)),
            Ty::Struct(id) => module.struct_def(*id).is_none_or(|definition| {
                definition
                    .fields
                    .iter()
                    .any(|field| walk(module, &field.ty, depth + 1))
            }),
            Ty::Record(id) => module.record_def(*id).is_none_or(|definition| {
                definition
                    .fields
                    .iter()
                    .any(|field| walk(module, &field.ty, depth + 1))
            }),
            Ty::Closure(id) => module.closure_type(*id).is_none_or(|definition| {
                definition
                    .captures
                    .iter()
                    .any(|capture| walk(module, capture, depth + 1))
            }),
            // An enum behind any pointer-like value is not stored by value in
            // that value. Function signatures likewise describe code-address
            // transport, not bytes reconstructed by this instruction.
            Ty::Ptr
            | Ty::FatPtr(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::Func(_)
            | Ty::FnItem(_)
            | Ty::Handle(_) => false,
            Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::Error
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Unit
            | Ty::Never
            | Ty::Dialect(_) => false,
            // A Storage value is module geometry rather than an ordinary
            // byte value, and the scanner separately refuses any module that
            // contains one. Keep this local instruction gate fail-closed too.
            Ty::Storage(_) => true,
            // Level-R's extension is uninhabited today; keeping this arm
            // fail-closed also makes a future extension unable to bypass the
            // enum-image gate silently.
            Ty::Ext(_) => true,
        }
    }

    walk(module, ty, 0)
}

fn carries_fn_item(value: &Constant) -> bool {
    value
        .try_visit_constants(|nested| {
            if matches!(nested, Constant::FnItem(_)) {
                std::ops::ControlFlow::Break(())
            } else {
                std::ops::ControlFlow::Continue(())
            }
        })
        .is_break()
}

fn unsupported_nonterminator_detail(module: &Module, inst: &Inst) -> Option<String> {
    match inst {
        Inst::MakeClosure { ty, func, captures } => {
            closure_construction_refusal(module, *ty, *func, captures.len())
        },
        // A direct call is admitted unless its callee is a symbol trust-cg
        // lowers with substituted semantics fsym does not model (see
        // `classify_call`); `visit_node` checks the admitted ones.
        Inst::Call { callee, args } => match classify_call(module, *callee, args.len()) {
            CallEffect::Refused { detail } => Some(detail),
            CallEffect::Bulk { .. }
            | CallEffect::ValueOnly
            | CallEffect::ModuleBody
            | CallEffect::External { .. }
            | CallEffect::Unresolved { .. } => None,
        },
        Inst::Undef { ty } => Some(format!(
            "Undef({ty:?}) requires poison/undef and NoUndef proof semantics"
        )),
        Inst::CallIndirect { .. } => {
            Some("CallIndirect requires callee/call-effect summaries".to_string())
        }
        // v53: a non-propagating call boundary obliges the consumer to stop an
        // unwind at the call site. fsym models no host unwinding (the
        // reference interpreter refuses the boundary too), and scanning it as
        // an ordinary call would erase the boundary.
        Inst::CallCannotUnwind { .. } | Inst::CallIndirectCannotUnwind { .. } => Some(
            "a non-propagating call boundary (CallCannotUnwind / CallIndirectCannotUnwind) \
             requires host-unwind semantics; fsym models none"
                .to_string(),
        ),
        // v67: the reference interpreter refuses a `BoxDeref` whose operand
        // is null, misaligned or outside a live allocation as undefined
        // behaviour. fsym has no obligation kind for a carried validity
        // fact, and scanning the instruction as a plain copy would owe no
        // verdict on those three sites while calling the function scanned.
        Inst::BoxDeref { .. } => Some(
            "a Box deref (BoxDeref) is undefined behaviour unless its operand is valid as a \
             Box; fsym models no validity-fact obligation"
                .to_string(),
        ),
        // v54 (amendment P): a sited check names the panic entry its failure
        // calls and the location it reports. fsym scans the reference
        // semantics, where a failed check is a terminal panic; it owes no
        // verdict on the entry call compiled code makes instead, so it
        // refuses the site rather than scan it as an unsited check.
        Inst::Assert { site: Some(_), .. } => Some(
            "a sited check (Assert with a v54 panic site) calls its panic entry on failure; \
             fsym models no panic-entry call"
                .to_string(),
        ),
        // v54: the sited check with an unwind edge is a terminator, refused by
        // `validate_function_scope` before this gate; named here too.
        Inst::AssertInvoke { .. } => Some(
            "AssertInvoke (a v54 sited check with an unwind edge) requires panic-entry and \
             host-unwind semantics; fsym models neither"
                .to_string(),
        ),
        // v55 / v56 (amendment D): terminators, refused by
        // `validate_function_scope` before this gate; named here too.
        Inst::DropInvoke { .. } => Some(
            "DropInvoke (a v55 drop with an unwind edge) runs the type's drop glue and \
             requires host-unwind semantics; fsym models no destructor and no unwinding"
                .to_string(),
        ),
        Inst::InvokeIndirect { .. } => Some(
            "InvokeIndirect (a v56 indirect call with an unwind edge) requires a callee \
             summary and host-unwind semantics; fsym models neither"
                .to_string(),
        ),
        Inst::Retain { .. } | Inst::Release { .. } | Inst::IsUnique { .. } => Some(
            "ARC retain/release/is_unique semantics are outside bounded fsym support".to_string(),
        ),
        Inst::TensorContract { .. } => Some(
            "TensorContract requires tensor value and shape semantics outside bounded fsym support".into(),
        ),
        Inst::TensorMap { .. } => Some(
            "TensorMap requires tensor lane, index and shape semantics outside bounded fsym support".into(),
        ),
        Inst::TensorReduce { .. } => Some(
            "TensorReduce requires tensor lane, index and shape semantics outside bounded fsym support".into(),
        ),
        Inst::TensorView { .. } => Some(
            "TensorView requires tensor lane, index and shape semantics outside bounded fsym support".into(),
        ),
        Inst::TensorGather { .. } => Some("TensorGather requires coordinate tensor and bounds semantics outside bounded fsym support".into()),
        Inst::TensorScatter { .. } => Some("TensorScatter requires coordinate tensor, bounds and row-major update semantics outside bounded fsym support".into()),
        Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. } => Some(
            "binding-frame ops require quantified frame semantics outside bounded fsym support"
                .to_string(),
        ),
        Inst::DialectOp(op) => Some(format!(
            "DialectOp `{}` requires dialect-specific semantics before fsym",
            op.qualified_name()
        )),
        // `SeqMap` runs its element function through the call machinery, once
        // per element: an indirect call fsym does not summarize.
        Inst::SeqMap { .. } => Some(
            "SeqMap calls its element function per element; fsym does not summarize it".to_string(),
        ),
        // v47: a drop runs the dropped type's destructor (it frees and can run
        // user code). fsym models no destructor. The reference interpreter
        // runs a drop as a call of its type's glue (v55, amendment D) and
        // refuses an unresolved one; fsym summarizes no such call.
        Inst::Drop { ty, .. } => Some(format!(
            "Drop({ty:?}) runs a destructor; fsym models no destructor"
        )),
        // v48: a WEAK compare-exchange may fail spuriously. fsym reasons with
        // the reference interpreter's semantics, which refuses a weak one
        // rather than step it as strong (that would delete executions).
        Inst::CmpXchg { weak: true, .. } => Some(
            "a weak CmpXchg may fail spuriously; fsym's model refuses it rather than step it as \
             strong"
                .to_string(),
        ),
        Inst::Load { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::CmpXchg {
            ty, weak: false, ..
        } if type_may_contain_enum_by_value(module, ty) => Some(format!(
            "{} reconstructs an enum-containing value from bytes; bounded fsym does not prove that the byte image names an inhabited variant",
            crate::fsym_ub_map::fsym_inst_variant_name(inst)
        )),
        Inst::Cast {
            src_ty, dst_ty, ..
        } if type_may_contain_enum_by_value(module, src_ty)
            || type_may_contain_enum_by_value(module, dst_ty) =>
        {
            Some(
                "Cast encodes or reconstructs an enum-containing value through bytes; bounded fsym does not prove that the byte image names an inhabited variant"
                    .to_string(),
            )
        }
        // Memory accesses: each owes null / bounds / use-after-free verdicts
        // in `visit_node` (and `MemCopy` a non-overlap verdict), and each is
        // enumerated by `reachable_obligation_sites`.
        Inst::Load { .. }
        | Inst::Store { .. }
        | Inst::AtomicLoad { .. }
        | Inst::AtomicStore { .. }
        | Inst::AtomicRMW { .. }
        | Inst::CmpXchg { weak: false, .. }
        | Inst::MemCopy { .. }
        | Inst::MemSet { .. } => None,
        Inst::Const { value, .. } if carries_fn_item(value) => Some(
            "Const of Constant::FnItem requires nominal target semantics outside bounded fsym support".into(),
        ),
        // trust-ir v70: a weight-blob constant (at any depth of the constant)
        // is a tensor value read from the module's blob table, which fsym does
        // not model: refused by name, never left to `constant_expr`'s decline.
        Inst::Const { value, .. } if carries_tensor_blob(value) => Some(
            "Const of a trust-ir v70 Constant::TensorBlob (a tensor weight blob) is outside bounded fsym support"
                .to_string(),
        ),
        // Values the scanner models (or deliberately leaves unmodeled, which
        // turns any later dereference through them into an Unknown), and the
        // lifetime events its use-after-free check consumes.
        Inst::Const { .. }
        | Inst::NullPtr
        | Inst::Alloca { .. }
        | Inst::HeapAlloc { .. }
        | Inst::Copy { .. }
        | Inst::Cast { .. }
        | Inst::BinOp { .. }
        | Inst::UnOp { .. }
        | Inst::Overflow { .. }
        | Inst::ICmp { .. }
        | Inst::Select { .. }
        | Inst::GEP { .. }
        | Inst::Assume { .. }
        | Inst::Dealloc { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. } => None,
        // Aggregate lanes and vector elements: each owes a lane / index
        // verdict (`check_field`, `check_element_index`).
        Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. } => None,
        // No memory access of their own: pure value construction or
        // projection, address formation without a dereference, and a fence.
        // Their results are not modeled, so a pointer they produce reaches
        // `check_null` without facts and records an Unknown. (Every UB the
        // reference interpreter can raise for them is in `fsym_ub_map`, which
        // this gate also consults.)
        Inst::FCmp { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::Fence { .. }
        | Inst::GlobalAddr { .. }
        | Inst::Assert { site: None, .. }
        | Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        | Inst::LandingPad { .. }
        | Inst::MakeAggregate { .. }
        // trust-ir v50: `[value; n]`, one operand whatever `n` is.
        | Inst::ArraySplat { .. } => None,
        // Terminators never reach this gate: `validate_function_scope`
        // refuses a terminator before the end of a block as `MalformedCfg`
        // and validates the final one against its own supported set.
        Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Return { .. }
        | Inst::Unreachable
        | Inst::CoroSuspend { .. }
        | Inst::Invoke { .. }
        | Inst::Resume { .. } => None,
    }
}

fn validate_switch_terminator(
    module: &Module,
    function: &Function,
    source: BlockId,
    value: ValueId,
    default: BlockId,
    default_args: &[ValueId],
    cases: &[SwitchCase],
) -> Result<(), FunctionSkip> {
    if cases.len() > FSYM_TRUST_IR_MAX_SWITCH_CASES {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::Switch,
            format!(
                "bb{} switch has {} case(s), over fsym bound {}",
                source.index(),
                cases.len(),
                FSYM_TRUST_IR_MAX_SWITCH_CASES
            ),
        ));
    }

    let Some(selector_ty) = function
        .typed_value(module, value)
        .map(|metadata| metadata.ty)
    else {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::Switch,
            format!(
                "bb{} switch selector value {} has no typed metadata",
                source.index(),
                value.index()
            ),
        ));
    };

    if switch_selector_width(&selector_ty).is_none() {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::Switch,
            format!(
                "bb{} switch selector type {:?} is outside bounded fsym support",
                source.index(),
                selector_ty
            ),
        ));
    }

    validate_edge_args(function, source, default, default_args)?;
    for case in cases {
        if !matches!(case.value, Constant::Int(_)) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Switch,
                format!(
                    "bb{} switch case constant {:?} is outside bounded fsym support",
                    source.index(),
                    case.value
                ),
            ));
        }
        validate_edge_args(function, source, case.target, &case.args)?;
    }

    Ok(())
}

fn validate_edge_args(
    function: &Function,
    source: BlockId,
    target: BlockId,
    args: &[ValueId],
) -> Result<(), FunctionSkip> {
    let Some(target_block) = function_block(function, target) else {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::MalformedCfg,
            format!("bb{} targets missing bb{}", source.index(), target.index()),
        ));
    };
    if target_block.params.len() != args.len() {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::MalformedCfg,
            format!(
                "bb{} passes {} arg(s) to bb{} with {} param(s)",
                source.index(),
                args.len(),
                target.index(),
                target_block.params.len()
            ),
        ));
    }
    Ok(())
}

fn function_block(function: &Function, block: BlockId) -> Option<&Block> {
    function
        .blocks
        .iter()
        .find(|candidate| candidate.id == block)
}

fn block_successors(block: &Block) -> Vec<BlockId> {
    let Some(last) = block.body.last() else {
        return Vec::new();
    };
    match &last.inst {
        Inst::Br { target, .. } => vec![*target],
        Inst::CondBr {
            then_target,
            else_target,
            ..
        } => vec![*then_target, *else_target],
        Inst::Switch { default, cases, .. } => {
            let mut successors = Vec::with_capacity(cases.len() + 1);
            successors.push(*default);
            successors.extend(cases.iter().map(|case| case.target));
            successors
        }
        _ => Vec::new(),
    }
}

fn cfg_backedges(function: &Function) -> Vec<CfgEdge> {
    fn visit(
        function: &Function,
        block: BlockId,
        visiting: &mut HashSet<BlockId>,
        visited: &mut HashSet<BlockId>,
        backedges: &mut HashSet<CfgEdge>,
    ) {
        if visiting.contains(&block) {
            return;
        }
        if visited.contains(&block) {
            return;
        }

        visiting.insert(block);
        if let Some(block_ref) = function_block(function, block) {
            for successor in block_successors(block_ref) {
                if visiting.contains(&successor) {
                    backedges.insert(CfgEdge {
                        source: block,
                        target: successor,
                    });
                } else {
                    visit(function, successor, visiting, visited, backedges);
                }
            }
        }
        visiting.remove(&block);
        visited.insert(block);
    }

    let mut backedges = HashSet::new();
    visit(
        function,
        function.entry,
        &mut HashSet::new(),
        &mut HashSet::new(),
        &mut backedges,
    );
    let mut backedges = backedges.into_iter().collect::<Vec<_>>();
    backedges.sort_by_key(|edge| (edge.source.index(), edge.target.index()));
    backedges
}

fn validate_bounded_loop_scope(
    module: &Module,
    function: &Function,
    target: ScanTarget,
    backedge: CfgEdge,
) -> Result<(), FunctionSkip> {
    let loop_blocks = natural_loop_blocks(function, backedge)?;
    validate_loop_header(function, backedge, &loop_blocks)?;
    validate_loop_edges(function, backedge, &loop_blocks)?;
    validate_static_loop_unroll(module, function, target, backedge, &loop_blocks)?;
    Ok(())
}

fn natural_loop_blocks(
    function: &Function,
    backedge: CfgEdge,
) -> Result<HashSet<BlockId>, FunctionSkip> {
    let predecessors = block_predecessors(function);
    let mut loop_blocks = HashSet::from([backedge.target]);
    let mut stack = vec![backedge.source];

    while let Some(block) = stack.pop() {
        if !loop_blocks.insert(block) {
            continue;
        }
        if let Some(preds) = predecessors.get(&block) {
            stack.extend(preds.iter().copied());
        }
    }

    for block in &loop_blocks {
        if *block == backedge.target {
            continue;
        }
        for predecessor in predecessors.get(block).into_iter().flatten() {
            if !loop_blocks.contains(predecessor) {
                return Err(FunctionSkip::new(
                    FsymTrustIrSkipReason::Loop,
                    format!(
                        "complex loop has entry from bb{} to bb{} instead of header bb{}",
                        predecessor.index(),
                        block.index(),
                        backedge.target.index()
                    ),
                ));
            }
        }
    }

    Ok(loop_blocks)
}

fn block_predecessors(function: &Function) -> HashMap<BlockId, Vec<BlockId>> {
    let mut predecessors: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for block in &function.blocks {
        for successor in block_successors(block) {
            predecessors.entry(successor).or_default().push(block.id);
        }
    }
    predecessors
}

fn validate_loop_header(
    function: &Function,
    backedge: CfgEdge,
    loop_blocks: &HashSet<BlockId>,
) -> Result<(), FunctionSkip> {
    let Some(header) = function_block(function, backedge.target) else {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::MalformedCfg,
            format!("loop header bb{} is missing", backedge.target.index()),
        ));
    };

    for (_, ty) in &header.params {
        if !loop_carried_ty_supported(ty) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop header bb{} carries unsupported state type {:?}",
                    header.id.index(),
                    ty
                ),
            ));
        }
    }

    let Some(terminator) = header.body.last() else {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::MalformedCfg,
            format!("loop header bb{} has no terminator", header.id.index()),
        ));
    };
    let Inst::CondBr {
        then_target,
        else_target,
        ..
    } = &terminator.inst
    else {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::Loop,
            format!(
                "loop header bb{} is not a conditional static-bound check",
                header.id.index()
            ),
        ));
    };

    let then_continues = loop_blocks.contains(then_target);
    let else_continues = loop_blocks.contains(else_target);
    if then_continues == else_continues {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::Loop,
            format!(
                "loop header bb{} must have exactly one loop continuation and one exit",
                header.id.index()
            ),
        ));
    }

    Ok(())
}

fn validate_loop_edges(
    function: &Function,
    backedge: CfgEdge,
    loop_blocks: &HashSet<BlockId>,
) -> Result<(), FunctionSkip> {
    for block_id in loop_blocks {
        let Some(block) = function_block(function, *block_id) else {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::MalformedCfg,
                format!("loop block bb{} is missing", block_id.index()),
            ));
        };

        if matches!(
            block.body.last().map(|node| &node.inst),
            Some(Inst::Switch { .. })
        ) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "switch-controlled loop at bb{} is outside bounded fsym support",
                    block.id.index()
                ),
            ));
        }

        for successor in block_successors(block) {
            let edge = CfgEdge {
                source: *block_id,
                target: successor,
            };
            if successor == backedge.target && edge != backedge {
                return Err(FunctionSkip::new(
                    FsymTrustIrSkipReason::Loop,
                    format!(
                        "loop has multiple edges to header bb{}",
                        backedge.target.index()
                    ),
                ));
            }
            if !loop_blocks.contains(&successor) && *block_id != backedge.target {
                return Err(FunctionSkip::new(
                    FsymTrustIrSkipReason::Loop,
                    format!(
                        "loop exits from bb{}; bounded fsym only supports header exits",
                        block_id.index()
                    ),
                ));
            }
        }
    }

    if backedge.source != backedge.target {
        let Some(latch) = function_block(function, backedge.source) else {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::MalformedCfg,
                format!("loop latch bb{} is missing", backedge.source.index()),
            ));
        };
        if !matches!(
            latch.body.last().map(|node| &node.inst),
            Some(Inst::Br { target, .. }) if *target == backedge.target
        ) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop latch bb{} must branch directly to header bb{}",
                    backedge.source.index(),
                    backedge.target.index()
                ),
            ));
        }
    }

    Ok(())
}

fn validate_static_loop_unroll(
    module: &Module,
    function: &Function,
    target: ScanTarget,
    backedge: CfgEdge,
    loop_blocks: &HashSet<BlockId>,
) -> Result<(), FunctionSkip> {
    let Some(entry) = function_block(function, function.entry) else {
        return Ok(());
    };
    let mut worklist = VecDeque::from([FunctionScan::new(module, function, entry, target)]);
    let mut states = 0;
    let mut backedge_count = 0;

    while let Some(mut scan) = worklist.pop_front() {
        states += 1;
        if states > FSYM_TRUST_IR_MAX_LOOP_VALIDATION_STATES {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop validation exceeded {} state(s); CFG is outside bounded fsym loop support",
                    FSYM_TRUST_IR_MAX_LOOP_VALIDATION_STATES
                ),
            ));
        }

        scan.run_block();
        let source = scan.block.id;
        // Walk exactly the paths `scan_function` will walk: validation that
        // dropped a successor would leave a loop reached only through it
        // unvalidated, and `scan_function` unbounded.
        let successors = successor_scans(scan).map_err(|detail| {
            FunctionSkip::new(FsymTrustIrSkipReason::UnsupportedTerminator, detail)
        })?;
        if successors.unmodeled && loop_blocks.contains(&source) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop control in bb{} is outside bounded fsym support",
                    source.index()
                ),
            ));
        }

        for successor in successors.edges {
            if successor.target == backedge.target {
                validate_static_loop_args(function, backedge.target, &successor)?;
            }
            if successor.source == backedge.source && successor.target == backedge.target {
                backedge_count += 1;
                if backedge_count > FSYM_TRUST_IR_MAX_LOOP_UNROLL_ITERATIONS {
                    return Err(FunctionSkip::new(
                        FsymTrustIrSkipReason::Loop,
                        format!(
                            "loop backedge bb{} -> bb{} exceeds fsym unroll bound {}; trip count is not statically bounded",
                            backedge.source.index(),
                            backedge.target.index(),
                            FSYM_TRUST_IR_MAX_LOOP_UNROLL_ITERATIONS
                        ),
                    ));
                }
            }

            let target = successor.target;
            let args = successor.args;
            enqueue_edge(successor.scan, target, &args, &mut worklist);
        }
    }

    Ok(())
}

fn validate_static_loop_args(
    function: &Function,
    header: BlockId,
    successor: &SuccessorScan<'_>,
) -> Result<(), FunctionSkip> {
    let Some(header_block) = function_block(function, header) else {
        return Ok(());
    };

    for ((param, ty), arg) in header_block.params.iter().zip(&successor.args) {
        if !loop_carried_ty_supported(ty) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop header bb{} param {} has unsupported state type {:?}",
                    header.index(),
                    param.index(),
                    ty
                ),
            ));
        }

        let Some(facts) = successor.scan.values.get(arg) else {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop edge bb{} -> bb{} passes unknown value {} to header param {}",
                    successor.source.index(),
                    successor.target.index(),
                    arg.index(),
                    param.index()
                ),
            ));
        };
        if facts.pointer.is_some() || !loop_carried_ty_supported(&facts.ty) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop edge bb{} -> bb{} carries unsupported state value {}",
                    successor.source.index(),
                    successor.target.index(),
                    arg.index()
                ),
            ));
        }
        let Some(expr) = facts.expr.as_ref() else {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop edge bb{} -> bb{} carries non-symbolic state value {}",
                    successor.source.index(),
                    successor.target.index(),
                    arg.index()
                ),
            ));
        };
        if eval_concrete_u64(expr).is_none() {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop edge bb{} -> bb{} carries non-static state value {}",
                    successor.source.index(),
                    successor.target.index(),
                    arg.index()
                ),
            ));
        }
    }

    Ok(())
}

fn loop_carried_ty_supported(ty: &Ty) -> bool {
    (ty.is_integer() || matches!(ty, Ty::Bool))
        && ty
            .bit_width()
            .is_some_and(|width| (1..=64).contains(&width))
}

#[derive(Debug, Clone, Default)]
struct FunctionScanReport {
    diagnostics: Vec<FsymTrustIrDiagnostic>,
    unknown_obligations: Vec<FsymTrustIrUnknown>,
    coverage_errors: Vec<FsymCoverageError>,
}

fn scan_function(
    module: &Module,
    function: &Function,
    target: ScanTarget,
    skipped_callees: Rc<HashMap<FuncId, String>>,
    module_facts: Arc<ModuleFacts>,
) -> FunctionScanReport {
    let mut report = FunctionScanReport::default();
    let mut worklist = VecDeque::new();
    let Some(entry) = function_block(function, function.entry) else {
        return report;
    };

    let mut first = FunctionScan::new(module, function, entry, target);
    first.skipped_callees = skipped_callees;
    first.module_facts = module_facts;
    worklist.push_back(first);
    let mut recorded_unknowns = HashSet::new();
    let mut states = 0usize;

    while let Some(mut scan) = worklist.pop_front() {
        states += 1;
        if states > FSYM_TRUST_IR_MAX_PATH_STATES {
            // Liveness bound: the remaining paths are unwalked, so the
            // function is Unknown by name — never clean.
            report.unknown_obligations.push(FsymTrustIrUnknown {
                kind: FsymTrustIrDiagnosticKind::ScanBound,
                label: format!("{} path-state bound", function.name),
                module: module.name.clone(),
                function: function.name.clone(),
                block: scan.block.id.index(),
                inst_index: 0,
                reason: format!(
                    "the walk exceeded {FSYM_TRUST_IR_MAX_PATH_STATES} path states; {} pending path(s) from bb{} on were not checked",
                    worklist.len() + 1,
                    scan.block.id.index()
                ),
                path_guards: Vec::new(),
                candidate_expression: None,
                solver_candidate: None,
            });
            break;
        }
        scan.run_block();
        report.diagnostics.append(&mut scan.diagnostics);
        // Paths that differ only in the arm taken at an unmodeled branch
        // carry identical path conditions, so a block after the join records
        // the same Unknown once per path. An exact duplicate adds nothing.
        for unknown in scan.unknown_obligations.drain(..) {
            if recorded_unknowns.insert(format!("{unknown:?}")) {
                report.unknown_obligations.push(unknown);
            }
        }
        report.coverage_errors.append(&mut scan.coverage_errors);
        let block = scan.block;
        match successor_scans(scan) {
            Ok(successors) => {
                for successor in successors.edges {
                    let target = successor.target;
                    let args = successor.args;
                    enqueue_edge(successor.scan, target, &args, &mut worklist);
                }
            }
            // Fail closed: blocks that cannot be reached by the walk would
            // have every obligation in them silently dropped.
            Err(detail) => report.coverage_errors.push(FsymCoverageError {
                module: module.name.clone(),
                function: function.name.clone(),
                block: block.id.index(),
                inst_index: block.body.len().saturating_sub(1),
                opcode: block
                    .body
                    .last()
                    .map_or("terminator", |node| terminator_opcode(&node.inst)),
                detail,
            }),
        }
    }

    report
}

#[derive(Debug, Clone)]
struct SuccessorScan<'a> {
    source: BlockId,
    target: BlockId,
    args: Vec<ValueId>,
    scan: FunctionScan<'a>,
}

/// The successor states a block terminator hands to the walk.
struct Successors<'a> {
    edges: Vec<SuccessorScan<'a>>,
    /// The branch condition or switch selector had no modeled value: every
    /// target was kept, none was guarded, and each successor path is marked
    /// (`FunctionScan::unmodeled_branch`).
    unmodeled: bool,
}

fn terminator_opcode(inst: &Inst) -> &'static str {
    match inst {
        Inst::Br { .. } => "Br",
        Inst::CondBr { .. } => "CondBr",
        Inst::Switch { .. } => "Switch",
        Inst::Return { .. } => "Return",
        Inst::Unreachable => "Unreachable",
        Inst::CoroSuspend { .. } => "CoroSuspend",
        Inst::Invoke { .. } => "Invoke",
        Inst::Resume { .. } => "Resume",
        Inst::AssertInvoke { .. } => "AssertInvoke",
        Inst::DropInvoke { .. } => "DropInvoke",
        Inst::InvokeIndirect { .. } => "InvokeIndirect",
        _ => "terminator",
    }
}

/// The successors of `scan`'s block, each carrying the path state for its
/// edge. NEVER drops a successor it cannot decide: an arm is omitted only
/// when a modeled guard makes it concretely infeasible. A condition or
/// selector with no modeled value (loaded from memory, a call result, a
/// value of a sort the path condition cannot hold, ...) forks to EVERY
/// target with no path fact added, marking each path as past an unmodeled
/// branch. `Err` names a terminator whose successors cannot be walked at all
/// (the caller records it as a coverage error or a skip, never a pass).
fn successor_scans<'a>(scan: FunctionScan<'a>) -> Result<Successors<'a>, String> {
    let source = scan.block.id;
    let Some(terminator) = scan.block.body.last().map(|node| node.inst.clone()) else {
        return Err(format!(
            "bb{} has no terminator; its successors cannot be walked",
            source.index()
        ));
    };

    match terminator {
        Inst::Br { target, args } => Ok(Successors {
            edges: vec![SuccessorScan {
                source,
                target,
                args,
                scan,
            }],
            unmodeled: false,
        }),
        Inst::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        } => {
            // A Bool or i1 condition is modeled; any other sort would become
            // an unsatisfiable guard on BOTH arms (`branch_arm_guard`) and
            // prune them, so it is treated as unmodeled instead.
            let branch_expr = scan
                .values
                .get(&cond)
                .and_then(|facts| facts.expr.clone())
                .filter(|expr| matches!(expr_sort(expr), Some(SmtSort::Bool | SmtSort::BitVec(1))));
            let Some(branch_expr) = branch_expr else {
                let marker = format!("bb{} CondBr condition v{}", source.index(), cond.index());
                return Ok(unmodeled_successors(
                    scan,
                    source,
                    &marker,
                    vec![(then_target, then_args), (else_target, else_args)],
                ));
            };
            let original_guard_len = scan.ctx.guards.len();
            let fork = scan.ctx.fork_branch(branch_expr);

            let mut successors = Vec::with_capacity(2);
            let mut then_scan = scan.clone();
            then_scan.ctx = fork.then_ctx;
            if !context_has_new_concrete_false_guard(&then_scan.ctx, original_guard_len) {
                successors.push(SuccessorScan {
                    source,
                    target: then_target,
                    args: then_args,
                    scan: then_scan,
                });
            }

            let mut else_scan = scan;
            else_scan.ctx = fork.else_ctx;
            if !context_has_new_concrete_false_guard(&else_scan.ctx, original_guard_len) {
                successors.push(SuccessorScan {
                    source,
                    target: else_target,
                    args: else_args,
                    scan: else_scan,
                });
            }
            Ok(Successors {
                edges: successors,
                unmodeled: false,
            })
        }
        Inst::Switch {
            value,
            default,
            default_args,
            cases,
            ..
        } => Ok(switch_successor_scans(
            scan,
            source,
            value,
            default,
            default_args,
            &cases,
        )),
        Inst::Return { .. } | Inst::Unreachable => Ok(Successors {
            edges: Vec::new(),
            unmodeled: false,
        }),
        other => Err(format!(
            "bb{} ends in {}, whose successors the bounded walk cannot follow",
            source.index(),
            terminator_opcode(&other)
        )),
    }
}

/// Every target of an undecided branch, each walked with no path fact added
/// and its path marked as past the unmodeled `marker`.
fn unmodeled_successors<'a>(
    scan: FunctionScan<'a>,
    source: BlockId,
    marker: &str,
    targets: Vec<(BlockId, Vec<ValueId>)>,
) -> Successors<'a> {
    let mut scan = scan;
    if scan.unmodeled_branch.is_none() {
        scan.unmodeled_branch = Some(marker.to_string());
    }
    Successors {
        edges: targets
            .into_iter()
            .map(|(target, args)| SuccessorScan {
                source,
                target,
                args,
                scan: scan.clone(),
            })
            .collect(),
        unmodeled: true,
    }
}

fn switch_successor_scans<'a>(
    scan: FunctionScan<'a>,
    source: BlockId,
    value: ValueId,
    default: BlockId,
    default_args: Vec<ValueId>,
    cases: &[SwitchCase],
) -> Successors<'a> {
    let unmodeled = |scan: FunctionScan<'a>, default_args: Vec<ValueId>| {
        let mut targets = Vec::with_capacity(cases.len() + 1);
        targets.extend(cases.iter().map(|case| (case.target, case.args.clone())));
        targets.push((default, default_args));
        unmodeled_successors(
            scan,
            source,
            &format!("bb{} Switch selector v{}", source.index(), value.index()),
            targets,
        )
    };
    let Some((selector, width)) = scan
        .values
        .get(&value)
        .and_then(|facts| facts.expr.clone())
        .and_then(|selector| {
            let width = selector
                .try_bv_width()
                .ok()
                .filter(|width| (1..=64).contains(width))?;
            Some((selector, width))
        })
    else {
        return unmodeled(scan, default_args);
    };
    let guards = cases
        .iter()
        .map(|case| switch_case_guard(&selector, width, &case.value))
        .collect::<Option<Vec<_>>>();
    let default_guard = switch_default_guard(&selector, width, cases);
    let (Some(guards), Some(default_guard)) = (guards, default_guard) else {
        return unmodeled(scan, default_args);
    };

    let mut successors = Vec::with_capacity(cases.len() + 1);
    for (case, guard) in cases.iter().zip(guards) {
        if let Some(successor) =
            guarded_successor_scan(scan.clone(), source, guard, case.target, case.args.clone())
        {
            successors.push(successor);
        }
    }
    if let Some(successor) =
        guarded_successor_scan(scan, source, default_guard, default, default_args)
    {
        successors.push(successor);
    }

    Successors {
        edges: successors,
        unmodeled: false,
    }
}

fn guarded_successor_scan<'a>(
    mut scan: FunctionScan<'a>,
    source: BlockId,
    guard: SmtExpr,
    target: BlockId,
    args: Vec<ValueId>,
) -> Option<SuccessorScan<'a>> {
    if guard_is_concrete_false(&guard) {
        return None;
    }
    scan.ctx.guards.push(guard);
    Some(SuccessorScan {
        source,
        target,
        args,
        scan,
    })
}

fn context_has_new_concrete_false_guard(ctx: &PathContext, original_guard_len: usize) -> bool {
    ctx.guards[original_guard_len..]
        .iter()
        .any(guard_is_concrete_false)
}

fn enqueue_edge<'a>(
    mut scan: FunctionScan<'a>,
    target: BlockId,
    args: &[ValueId],
    worklist: &mut VecDeque<FunctionScan<'a>>,
) {
    let Some(target_block) = function_block(scan.function, target) else {
        return;
    };
    bind_block_params(&mut scan, target_block, args);
    scan.block = target_block;
    scan.diagnostics.clear();
    scan.unknown_obligations.clear();
    worklist.push_back(scan);
}

fn bind_block_params(scan: &mut FunctionScan<'_>, target: &Block, args: &[ValueId]) {
    let arg_facts = args
        .iter()
        .map(|arg| scan.values.get(arg).cloned())
        .collect::<Vec<_>>();
    for ((param, ty), facts) in target.params.iter().zip(arg_facts) {
        let facts = facts.unwrap_or(ValueFacts {
            ty: ty.clone(),
            expr: None,
            pointer: None,
            variant: None,
            int_as_float: None,
            closure_captures: None,
        });
        scan.values.insert(*param, facts);
    }
}

impl<'a> FunctionScan<'a> {
    fn new(
        module: &'a Module,
        function: &'a Function,
        block: &'a Block,
        target: ScanTarget,
    ) -> Self {
        let mut values = HashMap::new();
        for (value, ty) in &block.params {
            values.insert(
                *value,
                parameter_facts(function, *value, ty, target.pointer_bits),
            );
        }

        Self {
            module,
            function,
            block,
            target,
            values,
            ctx: PathContext {
                guards: Vec::new(),
                witness_candidates: Vec::new(),
            },
            unmodeled_branch: None,
            uaf_events: Vec::new(),
            uaf_reported: false,
            init: HashMap::new(),
            escaped: HashSet::new(),
            havocked: HashMap::new(),
            untracked_free: None,
            passed_call: None,
            borrow_seen: None,
            skipped_callees: Rc::new(HashMap::new()),
            module_facts: Arc::new(ModuleFacts::default()),
            diagnostics: Vec::new(),
            unknown_obligations: Vec::new(),
            covered: HashSet::new(),
            coverage_errors: Vec::new(),
            #[cfg(test)]
            force_drop_deref: false,
        }
    }

    fn run_block(&mut self) {
        // Fail-closed deref-coverage invariant. Structurally enumerate every
        // reachable memory-access site in this block BEFORE walking it, then
        // after the walk assert each enumerated site recorded a verdict. A
        // reachable deref that produces no verdict is a dropped obligation:
        // the scanner would be asserting a safety it never proved (fail-open).
        // We record an `FsymCoverageError` instead so callers fail closed —
        // the same discipline as the opcode coverage_gate.
        self.covered.clear();
        let expected = reachable_obligation_sites(self.module, self.block);

        for (inst_index, node) in self.block.body.iter().enumerate() {
            if node.is_terminator() {
                if matches!(node.inst, Inst::Unreachable) {
                    self.check_unreachable(node, inst_index);
                }
                break;
            }
            self.visit_node(node, inst_index);
        }

        for (inst_index, opcode, kinds) in expected {
            for kind in kinds {
                if !self.covered.contains(&(inst_index, kind)) {
                    self.coverage_errors.push(FsymCoverageError {
                        module: self.module.name.clone(),
                        function: self.function.name.clone(),
                        block: self.block.id.index(),
                        inst_index,
                        opcode,
                        detail: format!(
                            "reachable {opcode} {} obligation recorded no Safe/Diagnostic/Unknown verdict",
                            kind.as_str()
                        ),
                    });
                }
            }
        }
    }

    fn visit_node(&mut self, node: &InstrNode, inst_index: usize) {
        if materializes_global(&node.inst) {
            self.check_global_materialization(node, inst_index);
        }
        match &node.inst {
            Inst::Const { ty, value } => {
                if is_pointer_like_ty(ty) {
                    let pointer = self.constant_pointer(value);
                    self.define_pointer(node, ty.clone(), Some(pointer));
                } else {
                    let expr = constant_expr(ty, value, self.target.pointer_bits);
                    self.define_value(node, ty.clone(), expr, None);
                    if let (Ty::Enum(_), Constant::Aggregate(elems)) = (ty, value) {
                        let variant = match elems.first() {
                            Some(Constant::Int(discriminant)) => {
                                self.variant_of_discriminant(ty, *discriminant)
                            }
                            _ => None,
                        };
                        self.set_variant(node, variant);
                    }
                }
            }
            Inst::NullPtr => {
                // A NotNull annotation on a literal null is a false claim: it
                // is not honored.
                let pointer =
                    PointerFacts::untracked(Some(SmtExpr::bv_const(0, FSYM_TRUST_IR_POINTER_BITS)));
                self.define_pointer(node, Ty::Ptr, Some(pointer));
            }
            Inst::Alloca { ty, count, align } => {
                self.check_allocation(node, inst_index, "Alloca", ty, *count, *align);
                let pointer = self.new_object(inst_index, ty, *count, *align, ObjectKind::Stack);
                self.define_pointer(node, Ty::Ptr, Some(pointer));
            }
            Inst::HeapAlloc {
                ty,
                count,
                align,
                origin,
            } => {
                self.check_allocation(node, inst_index, "HeapAlloc", ty, *count, *align);
                // The origin is fixed per allocation site, so the object's
                // kind carries it to every `Dealloc` that frees it. The split
                // is trust-ir's proved table `AllocOrigin::is_reference_counted`
                // (every cell a gate-13 law), the one the reference
                // interpreter's `Dealloc` reads: a new origin gets its
                // `Dealloc` meaning from that one statement on both sides.
                let kind = if origin.is_reference_counted() {
                    ObjectKind::RcHeap
                } else {
                    ObjectKind::Heap
                };
                let pointer = self.new_object(inst_index, ty, *count, *align, kind);
                self.define_pointer(node, Ty::Ptr, Some(pointer));
            }
            Inst::Copy { ty, operand } => {
                let facts = self.values.get(operand).cloned();
                let variant = facts.as_ref().and_then(|facts| facts.variant);
                let int_as_float = facts.as_ref().and_then(|facts| facts.int_as_float);
                let closure_captures = facts
                    .as_ref()
                    .filter(|facts| facts.ty == *ty && matches!(ty, Ty::Closure(_)))
                    .and_then(|facts| facts.closure_captures.clone());
                self.define_value(
                    node,
                    ty.clone(),
                    facts.as_ref().and_then(|facts| facts.expr.clone()),
                    facts.and_then(|facts| facts.pointer),
                );
                self.set_variant(node, variant);
                self.set_int_as_float(node, int_as_float);
                self.set_closure_captures(node, closure_captures);
            }
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => self.visit_cast(node, inst_index, *op, src_ty, dst_ty, *operand),
            Inst::BinOp { op, ty, lhs, rhs } => {
                self.check_arithmetic(node, inst_index, *op, ty, *lhs, *rhs);
                // Only the bitwise operators mean the same thing lane-wise
                // and on the whole vector; any other vector result stays
                // unmodeled rather than carry or shift across lanes.
                let expr = if matches!(ty, Ty::Vector(..))
                    && !matches!(op, BinOp::And | BinOp::Or | BinOp::Xor)
                {
                    None
                } else {
                    self.binop_expr(*op, *lhs, *rhs)
                };
                self.define_value(node, ty.clone(), expr, None);
            }
            Inst::UnOp { op, ty, operand } => {
                self.check_unary(node, inst_index, *op, ty, *operand);
                let expr = if matches!(ty, Ty::Vector(..)) {
                    None
                } else {
                    self.unop_expr(*op, *operand)
                };
                self.define_value(node, ty.clone(), expr, None);
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                // Pointer comparisons materialize BOTH numeric addresses in
                // the reference interpreter, just like pointer-to-int casts.
                // An unrepresentable address is UB even for an unused result.
                if *ty == Ty::Ptr {
                    self.check_address_exposure(node, inst_index, *lhs);
                    self.check_address_exposure(node, inst_index, *rhs);
                }
                // A pointer operand's `expr` is its EXACT address or nothing
                // (see `PointerFacts::addr`), so two pointers compare only by
                // exact addresses; a comparison involving a tracked object's
                // abstract address is unmodeled, and a branch on it walks both
                // arms with no path fact.
                let expr = self.icmp_expr(*op, *lhs, *rhs);
                self.define_value(node, Ty::Bool, expr, None);
            }
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                // The result carries no pointer facts: a tracked object
                // selected here is reachable through an untracked value.
                self.escape_value(*then_val);
                self.escape_value(*else_val);
                let expr = self.select_expr(*cond, *then_val, *else_val);
                self.define_value(node, ty.clone(), expr, None);
            }
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                // SOUNDNESS: deliberately ignore the producer's `inbounds`
                // claim. This is a memory-safety checker; trusting an
                // unverified no-wrap/in-bounds hint could suppress a genuine
                // out-of-bounds finding. The symbolic address is computed
                // conservatively from base + index*size and bounds are checked
                // independently regardless of this flag.
                inbounds: _,
            } => {
                let no_wrap = self.check_gep(node, inst_index, pointee_ty, *base, indices);
                let pointer = self.gep_pointer(pointee_ty, *base, indices, no_wrap);
                self.define_pointer(node, Ty::Ptr, pointer);
            }
            Inst::Load { ty, ptr, align, .. } => {
                self.check_access(node, inst_index, ty, *ptr, *align, MemoryAccess::Read);
                self.define_value(node, ty.clone(), None, None);
            }
            Inst::AtomicLoad { ty, ptr, .. } => {
                self.check_access(node, inst_index, ty, *ptr, None, MemoryAccess::Read);
                self.define_value(node, ty.clone(), None, None);
            }
            Inst::Store {
                ty,
                ptr,
                value,
                align,
                ..
            } => {
                self.store_value(node, inst_index, ty, *value);
                self.check_access(node, inst_index, ty, *ptr, *align, MemoryAccess::Write);
                self.store_init(*ptr, ty, Some(*value));
            }
            Inst::AtomicStore { ty, ptr, value, .. } => {
                self.store_value(node, inst_index, ty, *value);
                self.check_access(node, inst_index, ty, *ptr, None, MemoryAccess::Write);
                self.store_init(*ptr, ty, Some(*value));
            }
            Inst::AtomicRMW { ty, ptr, value, .. } => {
                self.store_value(node, inst_index, ty, *value);
                self.check_access(node, inst_index, ty, *ptr, None, MemoryAccess::ReadWrite);
                self.store_init(*ptr, ty, None);
                self.define_value(node, ty.clone(), None, None);
            }
            Inst::CmpXchg {
                ty, ptr, desired, ..
            } => {
                self.store_value(node, inst_index, ty, *desired);
                self.check_access(node, inst_index, ty, *ptr, None, MemoryAccess::ReadWrite);
                self.store_init(*ptr, ty, None);
                self.define_value(node, ty.clone(), None, None);
            }
            Inst::Dealloc { ptr } => {
                self.check_dealloc(node, inst_index, *ptr);
            }
            Inst::Assume { cond } => {
                if let Some(expr) = self.values.get(cond).and_then(|facts| facts.expr.clone()) {
                    self.ctx.guards.push(expr);
                }
            }
            Inst::Overflow { op, ty, lhs, rhs } => {
                self.define_overflow(node, *op, ty, *lhs, *rhs);
            }
            Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => {
                if self.borrow_seen.is_none() {
                    self.borrow_seen = Some(self.label(inst_index, "borrow"));
                }
                let source = self.values.get(ptr).cloned();
                let fat = self
                    .value_ty(*ptr)
                    .is_some_and(|ty| matches!(ty, Ty::FatPtr(_)));
                self.check_borrow(node, inst_index, *ptr, fat);
                let result_ty = source
                    .as_ref()
                    .map(|facts| facts.ty.clone())
                    .filter(|_| fat)
                    .unwrap_or(Ty::Ptr);
                self.define_value(
                    node,
                    result_ty,
                    source.as_ref().and_then(|facts| facts.expr.clone()),
                    source.and_then(|facts| facts.pointer),
                );
            }
            // Refused at admission (ARC; v47 Drop).
            Inst::IsUnique { .. } | Inst::Drop { .. } => {}
            Inst::Retain { ptr } | Inst::Release { ptr } | Inst::EndBorrow { borrow_ptr: ptr } => {
                if self
                    .values
                    .get(ptr)
                    .and_then(|facts| facts.pointer.as_ref())
                    .is_some_and(|pointer| pointer.object.is_some())
                {
                    self.check_uaf_event(node, inst_index, *ptr, UafEventKind::Use);
                }
            }
            Inst::MemSet { dst, bytes, .. } => {
                self.check_bulk_memory(
                    node,
                    inst_index,
                    BulkMemoryOp {
                        opcode: "MemSet",
                        dst: *dst,
                        src: None,
                        bytes: *bytes,
                        overlap_is_ub: false,
                    },
                );
            }
            Inst::MemCopy {
                dst,
                src,
                bytes,
                overlap,
            } => {
                self.check_bulk_memory(
                    node,
                    inst_index,
                    BulkMemoryOp {
                        opcode: "MemCopy",
                        dst: *dst,
                        src: Some(*src),
                        bytes: *bytes,
                        overlap_is_ub: !*overlap,
                    },
                );
            }
            Inst::Call { callee, args } => {
                self.visit_call(node, inst_index, *callee, args);
            }
            // Values built from operands: a tracked pointer placed in one is
            // reachable through an untracked value (a call handed it may free
            // the object), so it escapes. The results carry their type (and an
            // enum's active variant) but no value.
            // trust-ir v50 `[value; n]`: the element escapes exactly as a
            // `MakeAggregate` lane does; the result carries its type, no value.
            Inst::ArraySplat { ty, value } => {
                self.escape_value(*value);
                self.define_value(node, ty.clone(), None, None);
            }
            // Capture values are copied, never loaded or dereferenced. Keep
            // their facts only when every lane agrees with its declared type.
            // Escape each pointer conservatively: an unsummarized call may
            // reach it through this environment even after a copy/update.
            Inst::MakeClosure { ty, captures, .. } => {
                for capture in captures {
                    self.escape_value(*capture);
                }
                let facts = self
                    .module
                    .closure_type(*ty)
                    .filter(|closure| closure.captures.len() == captures.len())
                    .and_then(|closure| {
                        captures
                            .iter()
                            .zip(&closure.captures)
                            .map(|(value, ty)| {
                                self.values
                                    .get(value)
                                    .filter(|facts| facts.ty == *ty)
                                    .cloned()
                            })
                            .collect::<Option<Vec<_>>>()
                    });
                self.define_value(node, Ty::Closure(*ty), None, None);
                self.set_closure_captures(node, facts);
            }
            Inst::MakeAggregate {
                ty,
                variant,
                fields,
            } => {
                for field in fields {
                    self.escape_value(*field);
                }
                self.define_value(node, ty.clone(), None, None);
                if matches!(ty, Ty::Enum(_)) {
                    let variant = variant.filter(|variant| self.variant_is_distinct(ty, *variant));
                    self.set_variant(node, variant);
                }
            }
            // Aggregate lanes: the lane must exist in the value's shape — for
            // an enum, in its ACTIVE variant (trust-ir's
            // `check_enum_payload_lane`); rewriting an enum's tag is UB.
            Inst::ExtractField {
                ty,
                aggregate,
                field,
            } => {
                self.check_field(
                    node,
                    inst_index,
                    *aggregate,
                    *field,
                    Some(ty.clone()),
                    false,
                );
                let facts = self
                    .values
                    .get(aggregate)
                    .and_then(|facts| facts.closure_captures.as_ref())
                    .and_then(|captures| captures.get(*field as usize))
                    .filter(|facts| facts.ty == *ty)
                    .cloned();
                self.define_value(node, ty.clone(), None, None);
                if let (Some(result), Some(facts)) = (node.results.first(), facts) {
                    self.values.insert(*result, facts);
                }
            }
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } => {
                self.escape_value(*value);
                let lane_ty = self.value_ty(*value);
                self.check_field(node, inst_index, *aggregate, *field, lane_ty, true);
                // A lane write never changes an enum's tag.
                let variant = self.values.get(aggregate).and_then(|facts| facts.variant);
                let captures = self
                    .values
                    .get(aggregate)
                    .filter(|facts| facts.ty == *ty)
                    .and_then(|facts| facts.closure_captures.clone())
                    .and_then(|mut captures| {
                        let lane = captures.get_mut(*field as usize)?;
                        let value = self.values.get(value).filter(|value| value.ty == lane.ty)?;
                        *lane = value.clone();
                        Some(captures)
                    });
                self.define_value(node, ty.clone(), None, None);
                self.set_variant(node, variant);
                self.set_closure_captures(node, captures);
            }
            // Vector / array elements: the index must be non-negative and
            // below the element count (trust-ir's `runtime_index` and
            // `eval_extract_element`).
            Inst::ExtractElement { ty, array, index } => {
                self.check_element_index(node, inst_index, *array, *index);
                self.define_value(node, ty.clone(), None, None);
            }
            Inst::InsertElement {
                ty,
                array,
                index,
                value,
            } => {
                self.escape_value(*value);
                self.check_element_index(node, inst_index, *array, *index);
                self.define_value(node, ty.clone(), None, None);
            }
            Inst::PtrFromParts { data, .. } => {
                self.escape_value(*data);
            }
            // No memory access of their own (see `unsupported_nonterminator_detail`):
            // their results stay unmodeled, so a dereference through a pointer
            // they produce records an Unknown.
            Inst::FCmp { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::Fence { .. }
            | Inst::GlobalAddr { .. }
            | Inst::Assert { .. }
            | Inst::SeqMapAddK { .. }
            | Inst::SeqMapNot { .. }
            | Inst::SeqMap { .. }
            | Inst::LandingPad { .. } => {
                // A `GlobalAddr`'s placement verdicts were recorded above
                // (`check_global_materialization`); its pointer stays
                // unmodeled.
            }
            // Refused by the admission gate, so a scanned function never
            // contains them.
            Inst::Undef { .. }
            | Inst::CallIndirect { .. }
            | Inst::CallCannotUnwind { .. }
            | Inst::CallIndirectCannotUnwind { .. }
            | Inst::BoxDeref { .. }
            | Inst::OpenFrame { .. }
            | Inst::BindSlot { .. }
            | Inst::LoadSlot { .. }
            | Inst::CloseFrame { .. }
            | Inst::DialectOp(_)
            | Inst::TensorContract { .. }
            | Inst::TensorMap { .. }
            | Inst::TensorReduce { .. }
            | Inst::TensorView { .. }
            | Inst::TensorGather { .. }
            | Inst::TensorScatter { .. }
            | Inst::AssertInvoke { .. }
            | Inst::DropInvoke { .. }
            | Inst::InvokeIndirect { .. } => {}
            // `run_block` stops at the block terminator before visiting it;
            // successors are explored by `successor_scans`.
            Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Return { .. }
            | Inst::Unreachable
            | Inst::CoroSuspend { .. }
            | Inst::Invoke { .. }
            | Inst::Resume { .. } => {}
        }
    }

    /// Define a pointer-typed result: its `expr` is the pointer's EXACT
    /// address (or nothing), never an object identity.
    fn define_pointer(&mut self, node: &InstrNode, ty: Ty, pointer: Option<PointerFacts>) {
        let expr = pointer.as_ref().and_then(|pointer| pointer.addr.clone());
        self.define_value(node, ty, expr, pointer);
    }

    /// The facts of a pointer-typed constant. Zero is null. A nonzero
    /// constant is an exact address with NO provenance: an access through it
    /// is an Unknown (the reference interpreter refuses a nonzero `Ptr`
    /// constant outright, and the same address through `inttoptr` names no
    /// allocation). A constant the target's pointers cannot hold (negative,
    /// or past a 32-bit address space) has no modeled address at all.
    fn constant_pointer(&self, value: &Constant) -> PointerFacts {
        let Constant::Int(address) = value else {
            return PointerFacts::untracked(None);
        };
        let limit = match self.target.pointer_bits {
            Some(bits) if bits < 64 => (1u128 << bits) - 1,
            _ => u128::from(u64::MAX),
        };
        let addr = u128::try_from(*address)
            .ok()
            .filter(|address| *address <= limit)
            .map(|address| SmtExpr::bv_const(address as u64, FSYM_TRUST_IR_POINTER_BITS));
        PointerFacts::untracked(addr)
    }

    fn visit_cast(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        op: CastOp,
        src_ty: &Ty,
        dst_ty: &Ty,
        operand: ValueId,
    ) {
        let source = self.values.get(&operand).cloned();
        let pointer_bits = self.target.pointer_bits;
        let handle = src_ty.contains_handle() || dst_ty.contains_handle();
        match (is_pointer_like_ty(src_ty), is_pointer_like_ty(dst_ty)) {
            // Pointer to pointer: the same address and provenance. Only a
            // `Bitcast` or `PtrToPtr` of a non-handle type keeps the facts. A
            // result without them (a `Transmute`, which the reference
            // interpreter returns verbatim, or a handle) still holds the
            // object's address, so the object escapes, as through a pointer
            // to integer cast: a later call must havoc its retained facts.
            (true, true) => {
                let tracked = !handle && matches!(op, CastOp::Bitcast | CastOp::PtrToPtr);
                let pointer = source.and_then(|source| source.pointer);
                if !tracked
                    && let Some(object) = pointer.as_ref().and_then(|pointer| pointer.object)
                {
                    self.escaped.insert(object.id);
                }
                self.define_pointer(node, dst_ty.clone(), pointer.filter(|_| tracked));
            }
            // Pointer to integer: exposes the address. The integer is the
            // EXACT address when the pointer has one (at 64-bit pointers,
            // `cast_expr`); a tracked object's address is abstract, so the
            // integer is unmodeled. Either way the object's address escapes.
            (true, false) => {
                self.check_address_exposure(node, inst_index, operand);
                if let Some(object) = source
                    .as_ref()
                    .and_then(|source| source.pointer.as_ref())
                    .and_then(|pointer| pointer.object)
                {
                    self.escaped.insert(object.id);
                }
                let expr = source.as_ref().and_then(|source| {
                    cast_expr(op, src_ty, dst_ty, source.expr.clone()?, pointer_bits)
                });
                self.define_value(node, dst_ty.clone(), expr, None);
            }
            // Integer to pointer: an exact address (when modeled) with NO
            // tracked provenance.
            (false, true) => {
                self.check_integer_address(node, inst_index, src_ty, operand);
                let addr = source.as_ref().and_then(|source| {
                    cast_expr(op, src_ty, dst_ty, source.expr.clone()?, pointer_bits)
                });
                let pointer = (!handle).then(|| PointerFacts::untracked(addr));
                self.define_pointer(node, dst_ty.clone(), pointer);
            }
            (false, false) => {
                if float_to_int_has_ub(op) {
                    self.check_float_to_int(node, inst_index, op, dst_ty, operand);
                }
                let expr = source.as_ref().and_then(|source| {
                    cast_expr(op, src_ty, dst_ty, source.expr.clone()?, pointer_bits)
                });
                self.define_value(node, dst_ty.clone(), expr, None);
                if matches!(op, CastOp::SIToFP | CastOp::UIToFP) {
                    let significand = match dst_ty {
                        Ty::F64 => Some(53),
                        Ty::F32 => Some(24),
                        _ => None,
                    };
                    let origin =
                        significand
                            .zip(self.int_width(src_ty))
                            .map(|(significand, bits)| IntAsFloat {
                                signed: op == CastOp::SIToFP,
                                bits,
                                exact: bits <= significand,
                            });
                    self.set_int_as_float(node, origin);
                }
            }
        }
    }

    /// A raw float-to-integer conversion (`fptosi` / `fptoui`): trust-ir
    /// defines NaN and a value outside the destination's range as UB (the
    /// reference interpreter's `eval_cast`: `[-2^(n-1), 2^(n-1))` signed,
    /// `[0, 2^n)` unsigned; ub-numerics-policy section 2). Decided only for
    /// an operand whose value the scanner knows exactly (a float constant);
    /// anything else is an Unknown by name — IEEE arithmetic produces NaN
    /// and infinities without trapping, so no float value is safe unseen.
    fn check_float_to_int(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        op: CastOp,
        dst_ty: &Ty,
        operand: ValueId,
    ) {
        let message = format!("UB in `{op}`: NaN or a value outside the destination's range");
        let value = self
            .values
            .get(&operand)
            .and_then(|facts| facts.expr.as_ref())
            .and_then(
                |expr| match expr.try_eval(&HashMap::<String, u64>::new()).ok()? {
                    EvalResult::Float(value) => Some(value),
                    _ => None,
                },
            );
        let origin = self
            .values
            .get(&operand)
            .and_then(|facts| facts.int_as_float);
        let verdict = match (value, self.int_width(dst_ty)) {
            // An integer converted to a float and back (`x as f64 as i32`):
            // never NaN, and within the destination's range whenever every
            // value of the source integer is — after rounding, which is
            // monotone and reaches at most the next power of two.
            (None, Some(bits)) if origin.is_some() => {
                let origin = origin.expect("matched Some");
                let fits = match (op, origin.signed) {
                    (CastOp::FPToSI, true) => {
                        origin.bits < bits || (origin.bits == bits && origin.exact)
                    }
                    (CastOp::FPToSI, false) => {
                        origin.bits + 1 < bits || (origin.bits + 1 == bits && origin.exact)
                    }
                    (_, false) => origin.bits < bits || (origin.bits == bits && origin.exact),
                    // A negative source converts to a negative float, which
                    // an unsigned conversion cannot hold.
                    (_, true) => false,
                };
                if fits {
                    FsymVerdict::Safe
                } else {
                    FsymVerdict::Unknown {
                        reason: format!(
                            "the float holds a {}-bit {} integer, not provably within the destination's range",
                            origin.bits,
                            if origin.signed { "signed" } else { "unsigned" }
                        ),
                    }
                }
            }
            (Some(value), Some(bits)) if (1..=128).contains(&bits) => {
                let (lo, hi) = if op == CastOp::FPToUI {
                    (0.0, 2f64.powi(bits as i32))
                } else {
                    let half = 2f64.powi(bits as i32 - 1);
                    (-half, half)
                };
                if value.is_nan() || value < lo || value >= hi {
                    FsymVerdict::Ub {
                        witness: HashMap::new(),
                    }
                } else {
                    FsymVerdict::Safe
                }
            }
            (Some(_), _) => FsymVerdict::Unknown {
                reason: format!("the destination {dst_ty:?} has no modeled integer width"),
            },
            (None, _) => FsymVerdict::Unknown {
                reason: "the operand's float value is not modeled; cannot prove it a number within the destination's range".to_string(),
            },
        };
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::Arithmetic,
            message,
            verdict,
            (None, None),
        );
    }

    /// The type of `value`: from its facts, else from the function's typed
    /// value table.
    fn value_ty(&self, value: ValueId) -> Option<Ty> {
        self.values
            .get(&value)
            .map(|facts| facts.ty.clone())
            .or_else(|| {
                self.function
                    .typed_value(self.module, value)
                    .map(|metadata| metadata.ty)
            })
    }

    /// Record the integer origin of the float `node` just defined.
    fn set_int_as_float(&mut self, node: &InstrNode, origin: Option<IntAsFloat>) {
        if let Some(facts) = node
            .results
            .first()
            .and_then(|result| self.values.get_mut(result))
        {
            facts.int_as_float = origin;
        }
    }

    /// Record the active variant of the enum value `node` just defined.
    fn set_variant(&mut self, node: &InstrNode, variant: Option<u32>) {
        if let Some(facts) = node
            .results
            .first()
            .and_then(|result| self.values.get_mut(result))
        {
            facts.variant = variant;
        }
    }

    /// The effective discriminants of an enum type, when they name each
    /// variant exactly once (the only case in which a tag identifies its
    /// variant).
    fn enum_discriminants(&self, ty: &Ty) -> Option<Vec<i128>> {
        let Ty::Enum(id) = ty else {
            return None;
        };
        let discriminants = self.module.enum_def(*id)?.effective_discriminants()?;
        let distinct = discriminants
            .iter()
            .enumerate()
            .all(|(index, value)| !discriminants[..index].contains(value));
        distinct.then_some(discriminants)
    }

    /// The variant whose discriminant is `discriminant`.
    fn variant_of_discriminant(&self, ty: &Ty, discriminant: i128) -> Option<u32> {
        self.enum_discriminants(ty)?
            .iter()
            .position(|value| *value == discriminant)
            .and_then(|index| u32::try_from(index).ok())
    }

    /// Whether variant `variant` of `ty` is identified by its tag (so the
    /// interpreter's tag lookup lands on it, not on an earlier variant).
    fn variant_is_distinct(&self, ty: &Ty, variant: u32) -> bool {
        self.enum_discriminants(ty)
            .is_some_and(|discriminants| (variant as usize) < discriminants.len())
    }

    /// The payload lane types of each variant of an enum type.
    fn enum_variant_lanes(&self, ty: &Ty) -> Option<Vec<Vec<Ty>>> {
        let Ty::Enum(id) = ty else {
            return None;
        };
        Some(
            self.module
                .enum_def(*id)?
                .variants
                .iter()
                .map(|variant| variant.fields.clone())
                .collect(),
        )
    }

    /// `ExtractField` / `InsertField`: lane `field` must exist in the
    /// aggregate's shape. For a struct or tuple that is a static fact of its
    /// type; for an enum, lane 0 is the tag (never rewritable), and a payload
    /// lane must be a field of that type in the ACTIVE variant — the
    /// reference interpreter faults otherwise ("lane belongs to no field of
    /// active variant"). Decided exactly when every variant agrees, or when
    /// the active variant is known on this path; otherwise an Unknown.
    fn check_field(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        aggregate: ValueId,
        field: u32,
        lane_ty: Option<Ty>,
        insert: bool,
    ) {
        let kind = FsymTrustIrDiagnosticKind::OutOfBounds;
        let message = format!(
            "{} of lane {field} outside the aggregate's (active) shape",
            if insert {
                "InsertField"
            } else {
                "ExtractField"
            }
        );
        let ub = || FsymVerdict::Ub {
            witness: HashMap::new(),
        };
        let unknown = |reason: String| FsymVerdict::Unknown { reason };
        let aggregate_ty = self.value_ty(aggregate);
        let verdict = match aggregate_ty.as_ref() {
            None => unknown("the aggregate's type is unknown".to_string()),
            Some(ty @ Ty::Enum(_)) => match (field, insert) {
                (0, true) => ub(),
                (0, false) => FsymVerdict::Safe,
                (lane, _) => match (self.enum_variant_lanes(ty), lane_ty) {
                    (Some(variants), Some(lane_ty)) => {
                        let fits =
                            |fields: &Vec<Ty>| fields.get(lane as usize - 1) == Some(&lane_ty);
                        let active = self.values.get(&aggregate).and_then(|facts| facts.variant);
                        match active.and_then(|variant| variants.get(variant as usize)) {
                            Some(fields) if fits(fields) => FsymVerdict::Safe,
                            Some(_) => ub(),
                            None if variants.iter().all(fits) => FsymVerdict::Safe,
                            None if !variants.iter().any(fits) => ub(),
                            None => unknown(format!(
                                "the enum value's active variant is not known on this path; lane {lane} as {lane_ty:?} belongs to some variants only"
                            )),
                        }
                    }
                    _ => unknown("the enum's variants or the lane's type are unknown".to_string()),
                },
            },
            Some(Ty::Tuple(lanes)) => {
                if (field as usize) < lanes.len() {
                    FsymVerdict::Safe
                } else {
                    ub()
                }
            }
            Some(Ty::Closure(id)) => match self.module.closure_type(*id) {
                Some(closure) if (field as usize) < closure.captures.len() => FsymVerdict::Safe,
                Some(_) => ub(),
                None => unknown(format!("closure {id:?} is not defined in the module")),
            },
            Some(Ty::Struct(id)) => match self.module.struct_def(*id) {
                Some(def) if (field as usize) < def.fields.len() => FsymVerdict::Safe,
                Some(_) => ub(),
                None => unknown(format!("struct {id:?} is not defined in the module")),
            },
            Some(ty) => unknown(format!(
                "lane {field} of {ty:?}: the scanner does not model this aggregate's shape"
            )),
        };
        self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
    }

    /// `ExtractElement` / `InsertElement`: the index must be non-negative and
    /// below the element count of the vector / array (tuple) it indexes.
    fn check_element_index(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        array: ValueId,
        index: ValueId,
    ) {
        let kind = FsymTrustIrDiagnosticKind::OutOfBounds;
        let message = "element index out of range";
        let len = match self.value_ty(array) {
            Some(Ty::Vector(_, len)) => Some(u64::from(len)),
            Some(Ty::Array(_, len)) => Some(len),
            Some(Ty::Tuple(lanes)) => Some(lanes.len() as u64),
            _ => None,
        };
        let index_expr = self
            .values
            .get(&index)
            .and_then(|facts| widen_index_to_i64(facts.expr.clone()?, &facts.ty));
        let (Some(len), Some(index_expr)) = (len, index_expr) else {
            let verdict = FsymVerdict::Unknown {
                reason:
                    "the element count or the index is not modeled; cannot prove the index in range"
                        .to_string(),
            };
            self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
            return;
        };
        // A signed index is sign-extended: a negative one is a huge unsigned
        // offset, out of range like one past the end.
        let size = SmtExpr::bv_const(len, 64);
        let candidate_expression =
            format!("element index side condition: index={index_expr}, len={len}");
        let solver_obligation = bounds_solver_obligation(&index_expr, &size, 1);
        let verdict = check_oob_ub(
            &BoundsOp {
                label: self.label(inst_index, "element"),
                byte_offset: index_expr,
                object_size_bytes: size,
                access_size_bytes: 1,
                has_in_bounds_annotation: false,
            },
            &self.ctx,
        );
        self.record_verdict(
            node,
            inst_index,
            kind,
            message,
            verdict,
            (Some(candidate_expression), solver_obligation),
        );
    }

    /// `Borrow` / `BorrowMut` of a thin pointer: the reference interpreter
    /// faults on null ("null pointer dereference") and on a pointer with no
    /// allocation provenance. A borrow of a fat pointer is a pass-through.
    fn check_borrow(&mut self, node: &InstrNode, inst_index: usize, ptr: ValueId, fat: bool) {
        let provenance = FsymTrustIrDiagnosticKind::OutOfBounds;
        if fat {
            for kind in [FsymTrustIrDiagnosticKind::NullDeref, provenance] {
                self.record_verdict(
                    node,
                    inst_index,
                    kind,
                    "borrow of a fat pointer (a pass-through)",
                    FsymVerdict::Safe,
                    (None, None),
                );
            }
            return;
        }
        self.check_null_obligation(node, inst_index, ptr, "borrow of a null pointer", true);
        let pointer = self
            .values
            .get(&ptr)
            .and_then(|facts| facts.pointer.clone());
        if pointer.as_ref().and_then(exact_constant_address) == Some(0) {
            // Null: the null verdict just recorded carries the UB.
            self.covered.insert((inst_index, provenance));
            return;
        }
        let verdict = match &pointer {
            Some(pointer) if pointer.object.is_some() => FsymVerdict::Safe,
            Some(pointer) => FsymVerdict::Unknown {
                reason: format!(
                    "{}; a borrow of a pointer naming no allocation is UB",
                    untracked_reason(pointer)
                ),
            },
            None => FsymVerdict::Unknown {
                reason:
                    "pointer facts unavailable; cannot prove the borrowed pointer has provenance"
                        .to_string(),
            },
        };
        self.record_verdict(
            node,
            inst_index,
            provenance,
            "borrow of a pointer with no allocation provenance",
            verdict,
            (None, None),
        );
    }

    /// The value a store writes. A pointer value is encoded by its address
    /// (which must be representable: `check_address_exposure`) and makes its
    /// object reachable from memory.
    fn store_value(&mut self, node: &InstrNode, inst_index: usize, ty: &Ty, value: ValueId) {
        if ty_may_hold_address(self.module, ty) {
            self.check_address_exposure(node, inst_index, value);
        }
        self.escape_value(value);
    }

    /// Materializing a pointer's address as an integer (`ptrtoint`, a
    /// pointer-to-integer bitcast, storing or comparing a pointer value) computes
    /// `base + offset`; trust-ir defines it as UB when that leaves the
    /// address space ("pointer address overflow"). A tracked object's base is
    /// abstract, so only an offset the object's every placement names is
    /// provably representable (`offset_is_nameable`); an untracked pointer's
    /// address only when it is `nameable` (never a parameter's, see
    /// `PointerFacts::nameable`) and inside the target's address space.
    fn check_address_exposure(&mut self, node: &InstrNode, inst_index: usize, ptr: ValueId) {
        let message = "pointer address overflow";
        let unknown = |reason: String| FsymVerdict::Unknown { reason };
        let pointer = self
            .values
            .get(&ptr)
            .and_then(|facts| facts.pointer.clone());
        let verdict = match pointer {
            None => unknown(
                "pointer facts unavailable; cannot prove its address representable".to_string(),
            ),
            Some(pointer) => match pointer.object {
                Some(object) => match (
                    pointer.byte_offset.as_ref().and_then(eval_concrete_u64),
                    object.size_bytes,
                ) {
                    (Some(offset), Some(size))
                        if offset_is_nameable(self.target, u128::from(offset), size) =>
                    {
                        FsymVerdict::Safe
                    }
                    (Some(offset), Some(size)) if u128::from(offset) == u128::from(size) => {
                        unknown(format!(
                            "the pointer is one past the end of its {size}-byte object; on a {}-bit target the object may end exactly at the end of the address space, where that pointer has no address",
                            self.target.pointer_bits.unwrap_or(64)
                        ))
                    }
                    _ => unknown(
                        "the pointer may lie past its object, where base + offset may overflow the address space".to_string(),
                    ),
                },
                None => match &pointer.addr {
                    None => unknown(
                        "the pointer's address is not modeled; cannot prove it representable"
                            .to_string(),
                    ),
                    Some(_) if !pointer.nameable => unknown(
                        "the pointer has no tracked provenance, and its address is not proven one the interpreter computes (a parameter, or moved by a GEP whose no-wrap is not proven): it may lie so far past its allocation that base + offset has no address".to_string(),
                    ),
                    Some(addr) => match self.target.pointer_bits {
                        Some(bits) if bits < 64 => match eval_concrete_u64(addr) {
                            Some(address) if u128::from(address) < (1u128 << bits) => {
                                FsymVerdict::Safe
                            }
                            Some(_) => FsymVerdict::Ub {
                                witness: HashMap::new(),
                            },
                            None => unknown(format!(
                                "the address may exceed the {bits}-bit address space"
                            )),
                        },
                        // A nameable 64-bit address is its own representation.
                        _ => FsymVerdict::Safe,
                    },
                },
            },
        };
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::PointerArithmetic,
            message,
            verdict,
            (None, None),
        );
    }

    /// An integer turned into a pointer must be an address the target can
    /// name: any 64-bit value on a 64-bit target, at most `2^32 - 1` on a
    /// 32-bit one ("address is outside the target's address space").
    fn check_integer_address(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        src_ty: &Ty,
        operand: ValueId,
    ) {
        let limit_bits = self.target.pointer_bits.unwrap_or(64).min(64);
        let source = self.values.get(&operand);
        let source_width = source
            .and_then(|facts| facts.expr.as_ref())
            .and_then(|expr| expr.try_bv_width().ok())
            .or_else(|| self.int_width(src_ty));
        let verdict = match source_width {
            Some(width) if width <= limit_bits => FsymVerdict::Safe,
            _ => match source
                .and_then(|facts| facts.expr.as_ref())
                .and_then(eval_concrete_u64)
            {
                Some(address) if u128::from(address) < (1u128 << limit_bits) => FsymVerdict::Safe,
                Some(_) => FsymVerdict::Ub {
                    witness: HashMap::new(),
                },
                None => FsymVerdict::Unknown {
                    reason: format!(
                        "the integer may not be an address of the {limit_bits}-bit target"
                    ),
                },
            },
        };
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::PointerArithmetic,
            "integer is not a target address",
            verdict,
            (None, None),
        );
    }

    /// A stored/passed value makes every captured object's address reachable.
    /// Capture facts survive value copies and updates, so visit those lanes too.
    fn escape_value(&mut self, value: ValueId) {
        fn escape(facts: &ValueFacts, escaped: &mut HashSet<u64>) {
            if let Some(object) = facts.pointer.as_ref().and_then(|pointer| pointer.object) {
                escaped.insert(object.id);
            }
            if let Some(captures) = &facts.closure_captures {
                for capture in captures {
                    escape(capture, escaped);
                }
            }
        }
        if let Some(facts) = self.values.get(&value) {
            escape(facts, &mut self.escaped);
        }
    }

    /// A direct call, by `classify_call`: a bulk-memory symbol is checked
    /// exactly as `MemSet` / `MemCopy` are; every other call records one
    /// `UnsummarizedCall` verdict — `Safe` when the call's memory effects are
    /// accounted for, an Unknown by name when they are not. The call's
    /// results stay unmodeled, and every tracked object it may reach (handed
    /// to it, or escaped earlier) has its lifetime and contents havocked.
    fn visit_call(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        callee: FuncId,
        args: &[ValueId],
    ) {
        let effect = classify_call(self.module, callee, args.len());
        if let CallEffect::Bulk { symbol, kind } = effect
            && let [dst, second, bytes] = *args
        {
            self.check_bulk_memory(
                node,
                inst_index,
                BulkMemoryOp {
                    opcode: symbol,
                    dst,
                    src: (kind != BulkCallKind::Memset).then_some(second),
                    bytes,
                    overlap_is_ub: kind == BulkCallKind::Memcpy,
                },
            );
            return;
        }
        let callee_name = self
            .module
            .function_by_id(callee)
            .map_or_else(|| format!("f{}", callee.index()), |f| f.name.clone());
        let message = format!("unsummarized memory effect of call to `{callee_name}`");
        let carried = self.pointer_carrying_args(callee, args);
        let verdict = match effect.clone() {
            CallEffect::ValueOnly => FsymVerdict::Safe,
            CallEffect::ModuleBody => match (self.skipped_callees.get(&callee), carried.first()) {
                (Some(refusal), Some((index, ty))) => FsymVerdict::Unknown {
                    reason: format!(
                        "callee `{callee_name}` receives pointer-carrying argument #{index} ({ty}) but fsym does not scan it: {refusal}; its accesses through the argument are checked nowhere"
                    ),
                },
                _ => FsymVerdict::Safe,
            },
            CallEffect::External { replaceable } => match carried.first() {
                Some((index, ty)) => FsymVerdict::Unknown {
                    reason: format!(
                        "{} callee `{callee_name}` ({:?} linkage) receives pointer-carrying argument #{index} ({ty}); fsym has no summary of what it reads, writes or frees through it",
                        if replaceable {
                            "link-replaceable"
                        } else {
                            "external"
                        },
                        self.module
                            .function_by_id(callee)
                            .map(|function| function.linkage)
                            .unwrap_or_default()
                    ),
                },
                None => FsymVerdict::Safe,
            },
            CallEffect::Unresolved { reason } | CallEffect::Refused { detail: reason } => {
                FsymVerdict::Unknown { reason }
            }
            CallEffect::Bulk { symbol, .. } => FsymVerdict::Unknown {
                reason: format!("bulk-memory call `{symbol}` has {} argument(s)", args.len()),
            },
        };
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::UnsummarizedCall,
            message,
            verdict,
            (None, None),
        );
        if matches!(effect, CallEffect::ValueOnly) {
            return;
        }
        if self.passed_call.is_none() {
            self.passed_call = Some(callee_name.clone());
        }
        // A callee may free or overwrite whatever it can reach: the objects
        // handed to it and every object whose address escaped earlier.
        for arg in args {
            self.escape_value(*arg);
        }
        let reachable = self.escaped.iter().copied().collect::<Vec<_>>();
        for object in reachable {
            self.havocked
                .entry(object)
                .or_insert_with(|| callee_name.clone());
            self.init.remove(&object);
        }
    }

    /// The arguments of a call to `callee` that may carry a pointer, judged
    /// on the ARGUMENT's own type and facts AND on the callee's declared
    /// parameter type: whichever says pointer wins (an ill-typed declaration
    /// cannot launder a pointer argument into an integer), and an argument
    /// of unknown type counts.
    fn pointer_carrying_args(&self, callee: FuncId, args: &[ValueId]) -> Vec<(usize, String)> {
        let declared = self
            .module
            .function_by_id(callee)
            .and_then(|function| self.module.func_type(function.ty))
            .map(|signature| signature.params.clone())
            .unwrap_or_default();
        let mut carried = Vec::new();
        for (index, arg) in args.iter().enumerate() {
            let facts = self.values.get(arg);
            let arg_ty = facts.map(|facts| facts.ty.clone()).or_else(|| {
                self.function
                    .typed_value(self.module, *arg)
                    .map(|metadata| metadata.ty)
            });
            let described = match (&arg_ty, declared.get(index)) {
                (Some(ty), _) if ty_may_carry_pointer(ty) => format!("{ty:?}"),
                (_, Some(ty)) if ty_may_carry_pointer(ty) => format!("declared {ty:?}"),
                (None, _) => "an argument of unknown type".to_string(),
                _ if facts.is_some_and(|facts| facts.pointer.is_some()) => {
                    "an argument with pointer facts".to_string()
                }
                (Some(_), Some(_)) => continue,
                (Some(_), None) => "an argument past the declared parameters".to_string(),
            };
            carried.push((index, described));
        }
        carried
    }

    /// A fresh tracked allocation (`Alloca` / `HeapAlloc`): its own object,
    /// at offset 0, with an ABSTRACT address (no `addr`), its byte size when
    /// the element size and count are constants, and every byte
    /// uninitialized.
    fn new_object(
        &mut self,
        inst_index: usize,
        ty: &Ty,
        count: Option<ValueId>,
        align: Option<u64>,
        kind: ObjectKind,
    ) -> PointerFacts {
        let id = ((self.function.id.index() as u64 + 1) << 32)
            | ((self.block.id.index() as u64 + 1) << 16)
            | (inst_index as u64 + 1);
        let element_size = self.type_size_bytes(ty);
        // A non-constant count is at least one element (a count <= 0 is UB,
        // `check_alloc_count`), so one element is a sound LOWER bound on the
        // extent: every in-bounds claim against it holds for the real object.
        let count = match count {
            None => Some(1),
            Some(count) => self
                .values
                .get(&count)
                .and_then(|facts| {
                    let value = eval_concrete_u64(facts.expr.as_ref()?)?;
                    let width = facts.expr.as_ref()?.try_bv_width().ok()?;
                    (!facts.ty.is_signed() || value & (1u64 << (width - 1)) == 0).then_some(value)
                })
                .or(Some(1)),
        };
        let size_bytes = element_size.and_then(|size| size.checked_mul(count?));
        // A non-power-of-two alignment is malformed: no base alignment is
        // known from it.
        let base_align = match align {
            Some(align) if align.is_power_of_two() => Some(align),
            Some(_) => None,
            None => self.natural_align(ty),
        };

        // A fresh allocation: nothing about an earlier one from the same site
        // (a loop iteration) carries over.
        match size_bytes.filter(|size| *size <= FSYM_TRUST_IR_MAX_INIT_TRACKED_BYTES) {
            Some(size) => {
                self.init.insert(id, vec![false; size as usize]);
            }
            None => {
                self.init.remove(&id);
            }
        }
        self.escaped.remove(&id);
        self.havocked.remove(&id);

        PointerFacts {
            addr: None,
            object: Some(ObjectRef {
                id,
                kind,
                base_align,
                size_bytes,
            }),
            byte_offset: Some(SmtExpr::bv_const(0, 64)),
            object_size_bytes: size_bytes.map(|size| SmtExpr::bv_const(size, 64)),
            // A stack slot is never null. A heap allocation's null-ness is not
            // modeled (the allocator may fail), exactly as before it was
            // tracked.
            not_null_proven: kind == ObjectKind::Stack,
            // No `addr`: the object's base address is abstract.
            nameable: false,
        }
    }

    /// Materializing module globals (`GlobalAddr`, or a `Const` addressing a
    /// symbol): on a global's first use the interpreter allocates its storage
    /// at `max(natural, declared, 16)` alignment and writes its initializer's
    /// image (`global_pointer`). A global whose type has no layout is not
    /// placed at all, one whose size reaches
    /// `FSYM_TRUST_IR_MAX_MODELED_FOOTPRINT` overflows past the run model's
    /// budget, and at 64-bit pointers a placement past
    /// `FSYM_TRUST_IR_MAX_MODELED_ALIGN` may overflow the base address
    /// ("Alloca: base address overflow" — the BUDGET premise holds only up to
    /// it): all are Unknowns by name (kind `Arithmetic`, allocation
    /// placement); a modeled 64-bit placement is Safe only under the module's
    /// BUDGET premise (`under_budget_premise`). The initializer's address
    /// lanes are null or a window of a placed global (`symbol_pointer` checks
    /// the window, a type error otherwise); encoding one (kind
    /// `PointerArithmetic`) computes its address, which every placement names
    /// unless it is one past the global's end on a target whose address space
    /// the global may end with (`initializer_end_pointer`).
    fn check_global_materialization(&mut self, node: &InstrNode, inst_index: usize) {
        let bounded = self.target.end_may_be_unnameable();
        let globals = materialized_globals(self.module, &node.inst);
        let mut unmodeled = None;
        for &index in &globals {
            let Some(global) = self.module.globals.get(index) else {
                unmodeled = Some(format!(
                    "global #{index} does not resolve in the module; its placement is unknown"
                ));
                break;
            };
            if let Some(reason) =
                footprint_past_the_model(&global.ty, self.type_size_bytes(&global.ty))
            {
                unmodeled = Some(format!("global `{}`: {reason}", global.name));
                break;
            }
            match global_align(self.module, global) {
                Some(align) if bounded || align <= FSYM_TRUST_IR_MAX_MODELED_ALIGN => {}
                Some(align) => {
                    unmodeled = Some(format!(
                        "global `{}` is placed at alignment {align} (the max of its type's natural alignment, its declared alignment and 16), past the {FSYM_TRUST_IR_MAX_MODELED_ALIGN} bytes fsym models; its base may overflow the address space",
                        global.name
                    ));
                    break;
                }
                None => {
                    unmodeled = Some(format!(
                        "global `{}` has type {:?}, which has no reference-interpreter layout; its placement is unknown",
                        global.name, global.ty
                    ));
                    break;
                }
            }
        }
        let placement = match &unmodeled {
            None => self.under_budget_premise(FsymVerdict::Safe),
            Some(reason) => FsymVerdict::Unknown {
                reason: reason.clone(),
            },
        };
        let encoding = match unmodeled {
            Some(reason) => FsymVerdict::Unknown { reason },
            None if bounded => match initializer_end_pointer(self.module, &globals) {
                Some(reason) => FsymVerdict::Unknown { reason },
                None => placement.clone(),
            },
            None => placement.clone(),
        };
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::Arithmetic,
            "UB placing a module global's storage",
            placement,
            (None, None),
        );
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::PointerArithmetic,
            "UB encoding the addresses in a module global's initializer",
            encoding,
            (None, None),
        );
    }

    /// A placement verdict under the module's BUDGET premise (see the
    /// module docs): a modeled placement is free of base / next address
    /// overflow only while every allocation of the run is, so where the
    /// module may break the premise (`budget_premise_violation`, decided once
    /// per module scan) a `Safe` placement is an Unknown naming the
    /// instruction that breaks it. Concrete UB and Unknowns are kept.
    fn under_budget_premise(&self, verdict: FsymVerdict) -> FsymVerdict {
        // At 32-bit pointers no placement overflows, premise or not.
        if !matches!(verdict, FsymVerdict::Safe) || self.target.end_may_be_unnameable() {
            return verdict;
        }
        let violation = self
            .module_facts
            .budget_premise
            .get_or_init(|| budget_premise_violation(self.module));
        match violation {
            None => verdict,
            Some(violation) => FsymVerdict::Unknown {
                reason: format!(
                    "this placement is modeled, but its base and next address are free of overflow only while every allocation of the run is placed at an alignment of at most {FSYM_TRUST_IR_MAX_MODELED_ALIGN} (the BUDGET premise), and {violation}: a run through it can leave the interpreter's bump pointer anywhere"
                ),
            },
        }
    }

    /// The allocation verdict of an `Alloca` / `HeapAlloc`, owed at every
    /// one: its count — trust-ir defines a count `<= 0` and an overflowing
    /// byte size as UB ("Alloca: count must be positive", "allocation size
    /// overflow") — and its placement ("base / next address overflow"): an
    /// Unknown at an alignment fsym cannot lay out (explicit, else the type's
    /// NATURAL one, as the interpreter places it) and, at 64-bit pointers,
    /// past the modeled alignment; an Unknown too where its footprint (a
    /// `HeapAlloc`'s with the interpreter's usable-size slack) reaches
    /// `FSYM_TRUST_IR_MAX_MODELED_FOOTPRINT`; any other placement is Safe,
    /// at 64-bit pointers only under the module's BUDGET premise
    /// (`under_budget_premise`, see the module docs).
    fn check_allocation(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        opcode: &str,
        ty: &Ty,
        count: Option<ValueId>,
        align: Option<u64>,
    ) {
        let message = format!("arithmetic UB in `{opcode}` count or placement");
        let placement = allocation_align(self.module, ty, align);
        let bounded = self.target.end_may_be_unnameable();
        if placement.is_none_or(|align| !bounded && align > FSYM_TRUST_IR_MAX_MODELED_ALIGN) {
            let verdict = FsymVerdict::Unknown {
                reason: match (placement, align) {
                    (Some(placement), Some(_)) => format!(
                        "explicit alignment {placement} exceeds the {FSYM_TRUST_IR_MAX_MODELED_ALIGN} bytes fsym models; the object's base may overflow the address space"
                    ),
                    (Some(placement), None) => format!(
                        "{ty:?}'s natural alignment {placement} (the placement of an allocation with no explicit alignment) exceeds the {FSYM_TRUST_IR_MAX_MODELED_ALIGN} bytes fsym models; the object's base may overflow the address space"
                    ),
                    (None, _) => format!(
                        "the placement alignment of {ty:?} is unknown; the object's base may overflow the address space"
                    ),
                },
            };
            self.record_verdict(
                node,
                inst_index,
                FsymTrustIrDiagnosticKind::Arithmetic,
                message,
                verdict,
                (None, None),
            );
            return;
        }
        let slack = if opcode == "HeapAlloc" {
            FSYM_TRUST_IR_HEAP_SLACK
        } else {
            0
        };
        let footprint = |size: Option<u64>| size.and_then(|size| size.checked_add(slack));
        let Some(count) = count else {
            let verdict = match footprint_past_the_model(ty, footprint(self.type_size_bytes(ty))) {
                Some(reason) => FsymVerdict::Unknown { reason },
                None => self.under_budget_premise(FsymVerdict::Safe),
            };
            self.record_verdict(
                node,
                inst_index,
                FsymTrustIrDiagnosticKind::Arithmetic,
                message,
                verdict,
                (None, None),
            );
            return;
        };
        let facts = self.values.get(&count).cloned();
        let concrete = facts.as_ref().and_then(|facts| {
            let expr = facts.expr.as_ref()?;
            Some((
                eval_concrete_u64(expr)?,
                expr.try_bv_width().ok()?,
                facts.ty.is_signed(),
            ))
        });
        let verdict = match concrete {
            None => FsymVerdict::Unknown {
                reason: "allocation count is not a constant; cannot prove it positive and the size free of overflow".to_string(),
            },
            Some((value, width, signed)) => {
                let negative = signed && value & (1u64 << (width - 1)) != 0;
                if value == 0 || negative {
                    FsymVerdict::Ub {
                        witness: HashMap::new(),
                    }
                } else {
                    match self.type_size_bytes(ty) {
                        Some(size) => match size.checked_mul(value) {
                            None => FsymVerdict::Ub {
                                witness: HashMap::new(),
                            },
                            Some(bytes) => match footprint_past_the_model(ty, footprint(Some(bytes)))
                            {
                                Some(reason) => FsymVerdict::Unknown { reason },
                                None => FsymVerdict::Safe,
                            },
                        },
                        None => FsymVerdict::Unknown {
                            reason: format!(
                                "element size of {ty:?} is unknown; cannot prove the allocation size free of overflow"
                            ),
                        },
                    }
                }
            }
        };
        let verdict = self.under_budget_premise(verdict);
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::Arithmetic,
            message,
            verdict,
            (None, None),
        );
    }

    /// The byte delta of a one-index GEP (`sext/zext(index) * elem_size`, 64
    /// bits), when the index and element size are modeled.
    fn gep_delta(&self, pointee_ty: &Ty, index: ValueId) -> Option<SmtExpr> {
        let index_facts = self.values.get(&index)?;
        let index_expr = widen_index_to_i64(index_facts.expr.clone()?, &index_facts.ty)?;
        let elem_size = self.type_size_bytes(pointee_ty)?;
        Some(if elem_size == 1 {
            index_expr
        } else {
            index_expr.bvmul(SmtExpr::bv_const(elem_size, 64))
        })
    }

    /// The facts of a GEP result: the base's provenance, with the offset and
    /// exact address moved by the index. An offset or address that cannot be
    /// moved exactly becomes unmodeled — never left at the base's value. The
    /// moved address is `nameable` only when `no_wrap` (the GEP's address
    /// arithmetic was proven free of overflow on this path): past 2^64 the
    /// interpreter's offset still moves, and the pointer has no address.
    fn gep_pointer(
        &self,
        pointee_ty: &Ty,
        base: ValueId,
        indices: &[ValueId],
        no_wrap: bool,
    ) -> Option<PointerFacts> {
        let mut pointer = self.values.get(&base)?.pointer.clone()?;
        match indices {
            [] => {}
            [index] => {
                let delta = self.gep_delta(pointee_ty, *index);
                pointer.addr = pointer
                    .addr
                    .zip(delta.clone())
                    .map(|(addr, delta)| addr.bvadd(delta));
                pointer.byte_offset = pointer
                    .byte_offset
                    .zip(delta)
                    .map(|(offset, delta)| offset.bvadd(delta));
            }
            _ => {
                pointer.addr = None;
                pointer.byte_offset = None;
            }
        }
        pointer.nameable &= no_wrap;
        Some(pointer)
    }

    /// GEP obligations, as trust-ir's reference interpreter defines them: the
    /// base must not be null (`NullDeref`), a signed index must not be
    /// negative, and `base + index * elem_size` must not overflow 64 bits nor,
    /// on a 32-bit target, leave the address space — where the base's own
    /// address is computed too, so a base one past an object's end is
    /// checked even at index zero (`PointerArithmetic`). Returns whether the
    /// arithmetic was proven Safe (the result's address, when exact, is then
    /// one the interpreter computes: `gep_pointer`).
    fn check_gep(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        pointee_ty: &Ty,
        base: ValueId,
        indices: &[ValueId],
    ) -> bool {
        self.check_null_obligation(node, inst_index, base, "GEP on a null pointer", true);

        let message = "UB in GEP address arithmetic";
        let kind = FsymTrustIrDiagnosticKind::PointerArithmetic;
        let unknown = |reason: &str| FsymVerdict::Unknown {
            reason: reason.to_string(),
        };
        let pointer = self
            .values
            .get(&base)
            .and_then(|facts| facts.pointer.clone());
        let object = pointer.as_ref().and_then(|pointer| pointer.object);
        let end_unknown = |size: u64| {
            unknown(&format!(
                "the GEP's base or result is one past the end of its {size}-byte object; on a 32-bit target the object may end exactly at the end of the address space, where that pointer has no address"
            ))
        };
        let index = match indices {
            [] => {
                // No delta: only a 32-bit target computes (and checks) the
                // base's own address.
                let verdict = match (self.target.end_may_be_unnameable(), &pointer, object) {
                    (false, _, _) => FsymVerdict::Safe,
                    (true, Some(pointer), Some(object)) => match (
                        pointer.byte_offset.as_ref().and_then(eval_concrete_u64),
                        object.size_bytes,
                    ) {
                        (Some(offset), Some(size))
                            if offset_is_nameable(self.target, u128::from(offset), size) =>
                        {
                            FsymVerdict::Safe
                        }
                        (Some(offset), Some(size)) if offset == size => end_unknown(size),
                        _ => unknown(
                            "on a 32-bit target the GEP computes its base's address, and the base may lie past its object; not decided",
                        ),
                    },
                    (true, Some(pointer), None) if pointer.nameable && pointer.addr.is_some() => {
                        FsymVerdict::Safe
                    }
                    (true, _, _) => unknown(
                        "on a 32-bit target the GEP computes its base's address, which is not proven to be one the target names",
                    ),
                };
                let safe = matches!(verdict, FsymVerdict::Safe);
                self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
                return safe;
            }
            [index] => *index,
            _ => {
                let verdict = unknown("multi-index GEP offsets are not modeled");
                self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
                return false;
            }
        };
        let Some(elem_size) = self.type_size_bytes(pointee_ty) else {
            let verdict = unknown("GEP element size is unknown");
            self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
            return false;
        };
        let Some((index_expr, signed_index)) = self.values.get(&index).and_then(|facts| {
            Some((
                widen_index_to_i64(facts.expr.clone()?, &facts.ty)?,
                facts.ty.is_signed(),
            ))
        }) else {
            let verdict = unknown(
                "GEP index is not modeled; cannot prove it non-negative and the offset free of overflow",
            );
            self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
            return false;
        };
        // What the delta is added to: the offset within a tracked object, or
        // an exact address (which bounds any allocation offset from above).
        let base_expr = pointer.as_ref().and_then(|pointer| {
            if pointer.object.is_some() {
                pointer.byte_offset.clone()
            } else {
                pointer.addr.clone()
            }
        });
        let Some(base_expr) = base_expr else {
            let verdict =
                unknown("GEP base offset is not modeled; cannot prove the offset free of overflow");
            self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
            return false;
        };
        // The limit the result must stay within: the target's highest
        // address for an EXACT address (`2^32 - 1` on a 32-bit target — the
        // interpreter's `check_address`), `u64::MAX` for the offset within a
        // tracked object (the interpreter's `offset + delta` overflow). The
        // limit is in the kind, so the evaluator and the solver candidate
        // decide the same, target-width condition.
        let address_limit = match self.target.pointer_bits {
            Some(bits) if bits < 64 => (1u64 << bits) - 1,
            _ => u64::MAX,
        };
        let arith_kind = ArithUbKind::GepOffset {
            elem_size,
            signed_index,
            limit: if object.is_some() {
                u64::MAX
            } else {
                address_limit
            },
        };
        let candidate_expression = format!(
            "GEP side condition: index={index_expr}, elem_size={elem_size}, base={base_expr}"
        );
        let solver_obligation = FsymTrustIrSolverObligation::Arithmetic {
            kind: arith_kind,
            lhs: index_expr.clone(),
            rhs: Some(base_expr.clone()),
            width: 64,
        };
        let verdict = check_arith_ub(
            &ArithOp {
                label: self.label(inst_index, "gep"),
                kind: arith_kind,
                lhs: index_expr.clone(),
                rhs: base_expr.clone(),
                width: 64,
            },
            &self.ctx,
        );
        // Within a tracked object on a 32-bit target, the base's and the
        // result's ADDRESSES (an abstract base plus the offsets) must also be
        // in the address space. Decided only where both are offsets every
        // placement of the object names (`offset_is_nameable`: inside it, or
        // its base); otherwise an Unknown with NO solver candidate — no
        // candidate can encode an abstract base, and one encoding only the
        // 64-bit offset condition would let a solver "prove" a GEP the
        // interpreter faults on.
        if let Some(object) = object
            && self.target.end_may_be_unnameable()
        {
            let verdict = match verdict {
                FsymVerdict::Ub { witness } => FsymVerdict::Ub { witness },
                FsymVerdict::Safe | FsymVerdict::Unknown { .. } => {
                    let offsets = eval_concrete_u64(&index_expr)
                        .zip(eval_concrete_u64(&base_expr))
                        .map(|(index, base)| {
                            (
                                u128::from(base),
                                u128::from(index) * u128::from(elem_size) + u128::from(base),
                            )
                        });
                    match (offsets, object.size_bytes) {
                        (Some((base, end)), Some(size))
                            if offset_is_nameable(self.target, base, size)
                                && offset_is_nameable(self.target, end, size) =>
                        {
                            FsymVerdict::Safe
                        }
                        (Some((base, end)), Some(size))
                            if base <= u128::from(size) && end <= u128::from(size) =>
                        {
                            end_unknown(size)
                        }
                        _ => unknown(
                            "on a 32-bit target the GEP result may leave the address space (its object's base is abstract); not decided",
                        ),
                    }
                }
            };
            let safe = matches!(verdict, FsymVerdict::Safe);
            self.record_verdict(
                node,
                inst_index,
                kind,
                message,
                verdict,
                (Some(candidate_expression), None),
            );
            return safe;
        }
        let safe = matches!(verdict, FsymVerdict::Safe);
        self.record_verdict(
            node,
            inst_index,
            kind,
            message,
            verdict,
            (Some(candidate_expression), Some(solver_obligation)),
        );
        safe
    }

    /// Every obligation of one scalar access: not-null, in-bounds (with
    /// provenance), lifetime, alignment, and for a read the initialization of
    /// the bytes read. (A write's effect on initialization is `store_init`.)
    fn check_access(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        ty: &Ty,
        ptr: ValueId,
        align: Option<u64>,
        access: MemoryAccess,
    ) {
        self.check_null(node, inst_index, ptr);
        let exactly_null = self
            .values
            .get(&ptr)
            .and_then(|facts| facts.pointer.as_ref())
            .and_then(|pointer| pointer.addr.as_ref())
            .and_then(eval_concrete_u64)
            == Some(0);
        if exactly_null {
            // The access dereferences null: UB whenever it is reached, which
            // the null verdict just recorded carries (a diagnostic, or an
            // Unknown naming why reachability is open). Its other obligations
            // are moot: nothing about the object is reached.
            self.covered.extend(
                [
                    FsymTrustIrDiagnosticKind::OutOfBounds,
                    FsymTrustIrDiagnosticKind::UseAfterFree,
                    FsymTrustIrDiagnosticKind::Misaligned,
                    FsymTrustIrDiagnosticKind::Uninitialized,
                ]
                .map(|kind| (inst_index, kind)),
            );
            return;
        }
        self.check_bounds(node, inst_index, ty, ptr);
        let event = match access {
            MemoryAccess::Read => UafEventKind::Load,
            MemoryAccess::Write | MemoryAccess::ReadWrite => UafEventKind::Store,
        };
        self.check_lifetime(node, inst_index, ptr, event, true);
        self.check_alignment(node, inst_index, ty, ptr, align);
        if matches!(access, MemoryAccess::Read | MemoryAccess::ReadWrite) {
            self.check_init(node, inst_index, ty, ptr);
        }
    }

    /// The initialization a typed store of `ty` leaves at `ptr` (the
    /// interpreter's `eval_store`): the bytes the stored value's live fields
    /// cover are written initialized; padding and an enum's inactive-variant
    /// tail are written UNINITIALIZED, whatever they held before
    /// (`FsymLayout::written_coverage`; an enum's variant is the one the scanner
    /// tracked for `value`, else only its tag lane counts as written). At a
    /// constant offset exactly those bytes change; elsewhere a store that
    /// writes only initialized bytes marks nothing (an under-approximation),
    /// and one that writes padding may un-initialize any byte of the object,
    /// so none is proven initialized after it.
    fn store_init(&mut self, ptr: ValueId, ty: &Ty, value: Option<ValueId>) {
        let variant = value
            .and_then(|value| self.values.get(&value))
            .and_then(|facts| facts.variant);
        // The coverage costs the type's description, not its byte size; only
        // the bytes that fall inside the tracked object are visited.
        let coverage = FsymLayout::new(self.module)
            .written_coverage(ty, variant)
            .ok();
        let Some((id, offset)) = self.tracked_offset(ptr) else {
            return;
        };
        let Some(bits) = self.init.get_mut(&id) else {
            return;
        };
        match (offset, coverage) {
            (Some(offset), Some(coverage)) => {
                let end = offset
                    .saturating_add(coverage.size())
                    .min(bits.len() as u64);
                for position in offset.min(end)..end {
                    bits[position as usize] = coverage.contains(position - offset);
                }
            }
            (None, Some(coverage)) if coverage.covers_all() => {}
            _ => bits.iter_mut().for_each(|bit| *bit = false),
        }
    }

    fn check_null(&mut self, node: &InstrNode, inst_index: usize, ptr: ValueId) {
        self.check_null_obligation(node, inst_index, ptr, "null pointer dereference", true);
    }

    /// Record the not-null verdict for one dereference of `ptr`.
    ///
    /// Decided only on the pointer's EXACT address (`PointerFacts::addr`) or a
    /// not-null fact (a stack object, a NotNull annotation); an abstract
    /// address is never taken for a value. `escalate` attaches the typed
    /// solver candidate to an Unknown. A caller passes `false` when the
    /// current path guards include an opaque stand-in the solver must not
    /// treat as a real input (see `check_bulk_memory`).
    fn check_null_obligation(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        ptr: ValueId,
        message: &str,
        escalate: bool,
    ) {
        // Test-only fault injection: silently drop the obligation (the exact
        // shape of the regression this invariant guards against) so the
        // deref-coverage check can be tested for firing. No effect in release.
        #[cfg(test)]
        if self.force_drop_deref {
            return;
        }
        let Some(pointer) = self
            .values
            .get(&ptr)
            .and_then(|facts| facts.pointer.clone())
        else {
            // Fail closed: a reachable deref whose pointer has no modeled
            // facts is NOT safe. Record an Unknown instead of silently
            // returning — a missing model must never be an implicit
            // not-null proof. This also keeps the deref-coverage invariant
            // honest: the site is accounted for.
            self.record_unaccounted_deref(
                node,
                inst_index,
                FsymTrustIrDiagnosticKind::NullDeref,
                message,
                "pointer facts unavailable; cannot prove not-null",
            );
            return;
        };
        // Decided on the scanner's own facts only: a `NotNull` annotation is
        // a producer's claim that nothing here checks (a caller may hand the
        // function null), so it proves nothing (see the module docs).
        let known_not_null = pointer.not_null_proven;
        let Some(addr) = pointer.addr else {
            let verdict = if known_not_null {
                FsymVerdict::Safe
            } else {
                FsymVerdict::Unknown {
                    reason: "the pointer's address is not modeled; cannot prove not-null"
                        .to_string(),
                }
            };
            self.record_verdict(
                node,
                inst_index,
                FsymTrustIrDiagnosticKind::NullDeref,
                message,
                verdict,
                (None, None),
            );
            return;
        };
        let candidate_expression = addr.to_string();
        let solver_obligation = escalate.then(|| FsymTrustIrSolverObligation::NullDeref {
            ptr: addr.clone(),
            ptr_width: 64,
        });
        let verdict = check_null_deref(
            &MemOp {
                label: self.label(inst_index, "memory"),
                ptr: addr,
                ptr_width: 64,
                has_not_null_annotation: known_not_null,
            },
            &self.ctx,
        );
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::NullDeref,
            message,
            verdict,
            (Some(candidate_expression), solver_obligation),
        );
    }

    /// Check a bulk memory access (`MemCopy` / `MemSet`, or a direct call to
    /// a `memcpy` / `memmove` / `memset` symbol): an access of `bytes` bytes
    /// at `dst`, and for a copy also at `src`.
    ///
    /// Each accessed range owes what a `Store` / `Load` owes — a not-null, an
    /// in-bounds and a use-after-free verdict — and a non-overlapping
    /// `MemCopy` additionally owes a non-overlap verdict. trust-ir defines a
    /// zero-byte operation as a no-op even through a null or dangling pointer,
    /// so every obligation is conditional on `bytes != 0`:
    ///
    /// * a concrete zero count is recorded `Safe` (the defined no-op);
    /// * a concrete nonzero count is checked exactly;
    /// * a symbolic count adds the guard `bytes != 0` to the path, so the
    ///   evaluator can only answer `Safe` (independent of the count) or
    ///   `Unknown`, and a null-dereference solver candidate carries the guard;
    /// * a count with no modeled value is guarded by an opaque stand-in and no
    ///   solver candidate is attached, so it too can only be `Safe` or
    ///   `Unknown`.
    ///
    /// Whatever cannot be decided is recorded as an `Unknown` by name —
    /// never an implicit pass. Copying uninitialized bytes is defined (the
    /// destination bytes become uninitialized), so a bulk access owes no
    /// initialization verdict; it updates the destination's initialization.
    fn check_bulk_memory(&mut self, node: &InstrNode, inst_index: usize, op: BulkMemoryOp) {
        #[cfg(test)]
        if self.force_drop_deref {
            return;
        }
        let len = self.bulk_len(op.bytes);
        let (nonzero_guard, escalate) = match &len {
            BulkLen::Zero => {
                let mut kinds = vec![
                    FsymTrustIrDiagnosticKind::NullDeref,
                    FsymTrustIrDiagnosticKind::OutOfBounds,
                    FsymTrustIrDiagnosticKind::UseAfterFree,
                ];
                if op.overlap_is_ub && op.src.is_some() {
                    kinds.push(FsymTrustIrDiagnosticKind::Overlap);
                }
                for kind in kinds {
                    self.record_verdict(
                        node,
                        inst_index,
                        kind,
                        format!("zero-byte {}", op.opcode),
                        FsymVerdict::Safe,
                        (None, None),
                    );
                }
                return;
            }
            BulkLen::Concrete(_) => (None, true),
            BulkLen::Symbolic(bytes) => (Some(bytes.clone()), true),
            BulkLen::Unmodeled => (
                Some(SmtExpr::var(
                    format!(
                        "{}_bb{}_inst{}_unmodeled_bytes",
                        self.function.name,
                        self.block.id.index(),
                        inst_index
                    ),
                    64,
                )),
                false,
            ),
        };
        let original_guard_len = self.ctx.guards.len();
        if let Some(bytes) = nonzero_guard {
            let width = bytes.try_bv_width().unwrap_or(64);
            self.ctx
                .guards
                .push(bytes.eq_expr(SmtExpr::bv_const(0, width)).not_expr());
        }

        // The source is read before the destination is written.
        let mut accesses = Vec::with_capacity(2);
        if let Some(src) = op.src {
            accesses.push((src, "source", UafEventKind::Load));
        }
        accesses.push((op.dst, "destination", UafEventKind::Store));
        for (ptr, role, uaf_kind) in accesses {
            self.check_null_obligation(
                node,
                inst_index,
                ptr,
                &format!("null pointer dereference ({} {role})", op.opcode),
                escalate,
            );
            self.check_bulk_bounds(node, inst_index, ptr, &len, op.opcode, role);
            let definite = matches!(len, BulkLen::Concrete(_));
            self.check_lifetime(node, inst_index, ptr, uaf_kind, definite);
        }
        if op.overlap_is_ub
            && let Some(src) = op.src
        {
            self.check_bulk_overlap(node, inst_index, op.opcode, op.dst, src, &len);
        }

        self.ctx.guards.truncate(original_guard_len);

        // The destination's initialization after the access.
        let count = match len {
            BulkLen::Concrete(bytes) => Some(bytes),
            _ => None,
        };
        match op.src {
            None => self.mark_init(op.dst, count),
            Some(src) => self.copy_init(op.dst, src, count),
        }
    }

    /// The byte count of a bulk memory instruction, as far as it is modeled.
    fn bulk_len(&self, bytes: ValueId) -> BulkLen {
        let Some(expr) = self.values.get(&bytes).and_then(|facts| facts.expr.clone()) else {
            return BulkLen::Unmodeled;
        };
        if !expr
            .try_bv_width()
            .is_ok_and(|width| (1..=64).contains(&width))
        {
            return BulkLen::Unmodeled;
        }
        match eval_concrete_u64(&expr) {
            Some(0) => BulkLen::Zero,
            Some(bytes) => BulkLen::Concrete(bytes),
            None => BulkLen::Symbolic(expr),
        }
    }

    /// In-bounds verdict for one `len`-byte range of a bulk memory access.
    ///
    /// A range whose extent or count is unknown is recorded as an explicit
    /// Unknown. No `InBounds` annotation is honored: an annotation on the
    /// pointer speaks for its pointee-sized access, not for a `len`-byte
    /// range, and the one a producer puts on the bulk site is the obligation
    /// this check discharges, not a proof of it.
    fn check_bulk_bounds(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        ptr: ValueId,
        len: &BulkLen,
        opcode: &str,
        role: &str,
    ) {
        let pointer = self
            .values
            .get(&ptr)
            .and_then(|facts| facts.pointer.clone());
        let extent = pointer.as_ref().and_then(|pointer| {
            pointer.object?;
            Some((
                pointer.byte_offset.clone()?,
                pointer.object_size_bytes.clone()?,
            ))
        });
        let (access_size_bytes, (byte_offset, object_size_bytes)) = match (len, extent) {
            (BulkLen::Concrete(bytes), Some(extent)) => (*bytes, extent),
            (BulkLen::Concrete(bytes), None) => {
                let reason = match &pointer {
                    Some(pointer) if pointer.object.is_none() => untracked_reason(pointer),
                    _ => "object extent unavailable; cannot prove the accessed range in bounds",
                };
                self.record_unaccounted_deref(
                    node,
                    inst_index,
                    FsymTrustIrDiagnosticKind::OutOfBounds,
                    format!("out-of-bounds memory access ({bytes}-byte {opcode} {role} range)"),
                    reason,
                );
                return;
            }
            (BulkLen::Symbolic(count), Some((byte_offset, object_size_bytes))) => {
                self.check_symbolic_bulk_bounds(
                    node,
                    inst_index,
                    count,
                    byte_offset,
                    object_size_bytes,
                    &format!("{opcode} {role}"),
                );
                return;
            }
            (BulkLen::Symbolic(_), None) | (BulkLen::Unmodeled, _) => {
                self.record_unaccounted_deref(
                    node,
                    inst_index,
                    FsymTrustIrDiagnosticKind::OutOfBounds,
                    format!("out-of-bounds memory access ({opcode} {role} range)"),
                    "byte count is not a concrete constant; cannot prove the accessed range in bounds",
                );
                return;
            }
            (BulkLen::Zero, _) => return,
        };

        let candidate_expression = format!(
            "bounds side condition: offset={}, object_size={}, access_size={}",
            byte_offset, object_size_bytes, access_size_bytes
        );
        let solver_obligation =
            bounds_solver_obligation(&byte_offset, &object_size_bytes, access_size_bytes);
        let verdict = check_oob_ub(
            &BoundsOp {
                label: self.label(inst_index, "memory"),
                byte_offset,
                object_size_bytes,
                access_size_bytes,
                has_in_bounds_annotation: false,
            },
            &self.ctx,
        );
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::OutOfBounds,
            format!("out-of-bounds memory access ({access_size_bytes}-byte {opcode} {role} range)"),
            verdict,
            (Some(candidate_expression), solver_obligation),
        );
    }

    /// In-bounds verdicts for a `count`-byte range at `byte_offset` of a
    /// tracked object, `count` a modeled, non-constant byte count (nonzero on
    /// this path: `check_bulk_memory` guards it). The range is in bounds iff
    /// its start, its length and its end are: `offset <= size`,
    /// `count <= size` and `offset + count <= size` — three 64-bit bounds
    /// obligations (the start at width 0, the length's and the range's last
    /// byte at width 1). Each is decided (or escalated) on its own; together
    /// they are exact, since the first two keep the third from wrapping.
    fn check_symbolic_bulk_bounds(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        count: &SmtExpr,
        byte_offset: SmtExpr,
        object_size_bytes: SmtExpr,
        range: &str,
    ) {
        let count = match count.try_bv_width() {
            Ok(64) => count.clone(),
            Ok(width @ 1..=63) => count.clone().zero_ext(64 - width),
            _ => {
                self.record_unaccounted_deref(
                    node,
                    inst_index,
                    FsymTrustIrDiagnosticKind::OutOfBounds,
                    format!("out-of-bounds memory access ({range} range)"),
                    "byte count is not a 1..=64-bit integer; cannot prove the accessed range in bounds",
                );
                return;
            }
        };
        let one = || SmtExpr::bv_const(1, 64);
        for (what, offset, access_size_bytes) in [
            ("start", byte_offset.clone(), 0),
            ("length", count.clone().bvsub(one()), 1),
            ("end", byte_offset.bvadd(count).bvsub(one()), 1),
        ] {
            let candidate_expression = format!(
                "bounds side condition ({range} range {what}): offset={offset}, object_size={object_size_bytes}, access_size={access_size_bytes}"
            );
            let solver_obligation =
                bounds_solver_obligation(&offset, &object_size_bytes, access_size_bytes);
            let verdict = check_oob_ub(
                &BoundsOp {
                    label: self.label(inst_index, "memory"),
                    byte_offset: offset,
                    object_size_bytes: object_size_bytes.clone(),
                    access_size_bytes,
                    has_in_bounds_annotation: false,
                },
                &self.ctx,
            );
            self.record_verdict(
                node,
                inst_index,
                FsymTrustIrDiagnosticKind::OutOfBounds,
                format!("out-of-bounds memory access ({range} range {what})"),
                verdict,
                (Some(candidate_expression), solver_obligation),
            );
        }
    }

    /// Non-overlap verdict for a `memcpy`-semantics copy (`MemCopy` without
    /// `overlap`, or a call to a `memcpy` symbol).
    ///
    /// Decided only where the model is exact: two distinct tracked objects
    /// never overlap, whatever the count; within one object, concrete offsets
    /// and a concrete count decide it. Everything else is an Unknown.
    fn check_bulk_overlap(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        opcode: &str,
        dst: ValueId,
        src: ValueId,
        len: &BulkLen,
    ) {
        let message = format!("overlapping {opcode} source and destination ranges");
        let placement = |value: ValueId| {
            let pointer = self.values.get(&value)?.pointer.as_ref()?;
            let object = pointer.object?.id;
            let offset = pointer.byte_offset.as_ref().and_then(eval_concrete_u64);
            Some((object, offset))
        };
        let verdict = match (placement(dst), placement(src), len) {
            (Some((dst_object, _)), Some((src_object, _)), _) if dst_object != src_object => {
                FsymVerdict::Safe
            }
            (
                Some((_, Some(dst_offset))),
                Some((_, Some(src_offset))),
                BulkLen::Concrete(bytes),
            ) => {
                let (dst_offset, src_offset, bytes) = (
                    u128::from(dst_offset),
                    u128::from(src_offset),
                    u128::from(*bytes),
                );
                let overlaps = dst_offset < src_offset + bytes && src_offset < dst_offset + bytes;
                if !overlaps {
                    FsymVerdict::Safe
                } else if guards_hold(&self.ctx.guards, &HashMap::new()) {
                    FsymVerdict::Ub {
                        witness: HashMap::new(),
                    }
                } else {
                    FsymVerdict::Unknown {
                        reason: "ranges overlap; path condition not decided by the evaluator"
                            .to_string(),
                    }
                }
            }
            _ => FsymVerdict::Unknown {
                reason: "cannot decide whether the source and destination ranges overlap"
                    .to_string(),
            },
        };
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::Overlap,
            message,
            verdict,
            (None, None),
        );
    }

    /// In-bounds verdict for one scalar access. Never silent: an access
    /// through a pointer with no tracked provenance, or whose offset, extent
    /// or size is not modeled, is an Unknown by name. An `InBounds`
    /// annotation proves nothing — on the access (a claim about every caller,
    /// which nothing checks) or on the node that made the pointer (the LLVM
    /// importer turns `getelementptr inbounds` into one, and an `inbounds` GEP
    /// past its object yields poison, not an in-bounds pointer).
    fn check_bounds(&mut self, node: &InstrNode, inst_index: usize, ty: &Ty, ptr: ValueId) {
        let message = "out-of-bounds memory access";
        let kind = FsymTrustIrDiagnosticKind::OutOfBounds;
        let pointer = self
            .values
            .get(&ptr)
            .and_then(|facts| facts.pointer.clone());
        let unknown = |reason: &str| FsymVerdict::Unknown {
            reason: reason.to_string(),
        };
        let Some(pointer) = pointer else {
            let verdict = unknown("pointer facts unavailable; cannot prove the access in bounds");
            self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
            return;
        };
        if pointer.object.is_none() {
            let verdict = unknown(untracked_reason(&pointer));
            self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
            return;
        }
        let (Some(byte_offset), Some(object_size_bytes)) =
            (pointer.byte_offset, pointer.object_size_bytes)
        else {
            let verdict = unknown(
                "offset within, or extent of, the tracked object is not modeled; cannot prove the access in bounds",
            );
            self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
            return;
        };
        let Some(access_size_bytes) = self.type_size_bytes(ty) else {
            let verdict = unknown("size of the accessed type is unknown");
            self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
            return;
        };

        let candidate_expression = format!(
            "bounds side condition: offset={}, object_size={}, access_size={}",
            byte_offset, object_size_bytes, access_size_bytes
        );
        let solver_obligation =
            bounds_solver_obligation(&byte_offset, &object_size_bytes, access_size_bytes);
        let verdict = check_oob_ub(
            &BoundsOp {
                label: self.label(inst_index, "memory"),
                byte_offset: byte_offset.clone(),
                object_size_bytes: object_size_bytes.clone(),
                access_size_bytes,
                has_in_bounds_annotation: false,
            },
            &self.ctx,
        );
        self.record_verdict(
            node,
            inst_index,
            kind,
            message,
            verdict,
            (Some(candidate_expression), solver_obligation),
        );
    }

    /// Lifetime verdict for one access (or free) through `ptr`. A tracked
    /// object follows the per-path event stream; `definite` appends the
    /// access to it (a possibly-zero bulk access is checked against it but not
    /// recorded). An untracked pointer's object has an unknown lifetime (an
    /// `InBounds` proof on the access covers it: trust-ir's in-bounds
    /// predicate requires a live allocation). Past a call that may have
    /// freed the object, or a free of an untracked pointer, it is Unknown.
    fn check_lifetime(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        ptr: ValueId,
        kind: UafEventKind,
        definite: bool,
    ) {
        let message = "use after free or double free";
        let uaf = FsymTrustIrDiagnosticKind::UseAfterFree;
        let unknown = |reason: String| FsymVerdict::Unknown { reason };
        let pointer = self
            .values
            .get(&ptr)
            .and_then(|facts| facts.pointer.clone());
        let Some(object) = pointer.as_ref().and_then(|pointer| pointer.object) else {
            // No annotation stands in for the lifetime: an `InBounds` claim is
            // a precondition nothing checks (a caller may hand a freed block).
            let verdict = unknown(match &pointer {
                Some(pointer) => format!(
                    "{}; the lifetime of its object is unknown",
                    untracked_reason(pointer)
                ),
                None => "pointer facts unavailable; its object's lifetime is unknown".to_string(),
            });
            self.record_verdict(node, inst_index, uaf, message, verdict, (None, None));
            return;
        };
        if let Some(call) = self.havocked.get(&object.id).cloned() {
            let verdict = unknown(format!(
                "call `{call}` could reach this object and may have freed it"
            ));
            self.record_verdict(node, inst_index, uaf, message, verdict, (None, None));
            return;
        }
        if let Some(free) = self.untracked_free.clone() {
            let verdict = unknown(format!(
                "the earlier Dealloc at {free} of a pointer with no tracked provenance may have freed this object"
            ));
            self.record_verdict(node, inst_index, uaf, message, verdict, (None, None));
            return;
        }
        if definite {
            self.check_uaf_event(node, inst_index, ptr, kind);
            return;
        }
        if self.uaf_reported {
            // Accounted by the use-after-free already reported on this path.
            self.covered.insert((inst_index, uaf));
            return;
        }
        let object_expr = SmtExpr::bv_const(object.id, 64);
        let candidate_expression = object_expr.to_string();
        let mut events = self.uaf_events.clone();
        events.push(UafEvent {
            label: self.label(inst_index, "lifetime"),
            kind,
            object: object_expr,
        });
        let verdict = check_uaf_ub(&events, &self.ctx);
        if matches!(verdict, FsymVerdict::Ub { .. }) && self.unmodeled_branch.is_none() {
            self.uaf_reported = true;
        }
        self.record_verdict(
            node,
            inst_index,
            uaf,
            message,
            verdict,
            (Some(candidate_expression), None),
        );
    }

    /// Alignment verdict for one scalar access: its address must be a
    /// multiple of the explicit alignment, else of the accessed type's
    /// natural one. Decided from a tracked object's guaranteed base alignment
    /// and its offset, or from an exact address; otherwise Unknown.
    fn check_alignment(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        ty: &Ty,
        ptr: ValueId,
        align: Option<u64>,
    ) {
        let message = "misaligned memory access";
        let kind = FsymTrustIrDiagnosticKind::Misaligned;
        let unknown = |reason: String| FsymVerdict::Unknown { reason };
        let Some(access_align) = align.or_else(|| self.natural_align(ty)) else {
            let verdict = unknown(format!("alignment of {ty:?} is unknown"));
            self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
            return;
        };
        if access_align == 0 || !access_align.is_power_of_two() {
            let verdict = unknown(format!("alignment {access_align} is not a power of two"));
            self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
            return;
        }
        if access_align == 1 {
            self.record_verdict(
                node,
                inst_index,
                kind,
                message,
                FsymVerdict::Safe,
                (None, None),
            );
            return;
        }
        let pointer = self
            .values
            .get(&ptr)
            .and_then(|facts| facts.pointer.clone());
        let offset = match pointer.as_ref() {
            Some(pointer) => match (pointer.object, &pointer.addr) {
                (Some(object), _) => match (object.base_align, &pointer.byte_offset) {
                    (Some(base_align), Some(offset)) if base_align >= access_align => {
                        Ok(offset.clone())
                    }
                    (Some(base_align), _) if base_align < access_align => Err(format!(
                        "the access needs {access_align}-byte alignment; the object's base is guaranteed only {base_align}"
                    )),
                    _ => {
                        Err("the object's base alignment or the offset is not modeled".to_string())
                    }
                },
                (None, Some(addr)) => Ok(addr.clone()),
                (None, None) => Err("the pointer's address is not modeled".to_string()),
            },
            None => Err("pointer facts unavailable".to_string()),
        };
        let offset = match offset {
            Ok(offset) => offset,
            Err(reason) => {
                let verdict = unknown(format!("cannot prove the access aligned: {reason}"));
                self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
                return;
            }
        };
        let arith_kind = ArithUbKind::Misaligned {
            align: access_align,
        };
        let candidate_expression = format!("alignment side condition: {offset} % {access_align}");
        let solver_obligation = FsymTrustIrSolverObligation::Arithmetic {
            kind: arith_kind,
            lhs: offset.clone(),
            rhs: None,
            width: 64,
        };
        let verdict = check_arith_ub(
            &ArithOp {
                label: self.label(inst_index, "align"),
                kind: arith_kind,
                lhs: offset,
                rhs: SmtExpr::bv_const(0, 64),
                width: 64,
            },
            &self.ctx,
        );
        self.record_verdict(
            node,
            inst_index,
            kind,
            message,
            verdict,
            (Some(candidate_expression), Some(solver_obligation)),
        );
    }

    /// Initialization verdict for a read of `ty` at `ptr`: Safe only when
    /// every byte the read needs (`FsymLayout::read_coverage`: a scalar's every
    /// byte, an aggregate's live-field bytes) is proven written on this path
    /// (a tracked object of constant size, a constant offset — or any offset
    /// into a fully initialized object). Loading uninitialized bytes yields
    /// poison whose inspection is UB, so anything unproven is an Unknown by
    /// name.
    fn check_init(&mut self, node: &InstrNode, inst_index: usize, ty: &Ty, ptr: ValueId) {
        let message = "read of possibly uninitialized memory";
        let kind = FsymTrustIrDiagnosticKind::Uninitialized;
        let pointer = self
            .values
            .get(&ptr)
            .and_then(|facts| facts.pointer.clone());
        let needed = FsymLayout::new(self.module).read_coverage(ty).ok();
        let verdict = match self.init_state(pointer.as_ref(), needed.as_ref()) {
            Ok(()) => FsymVerdict::Safe,
            Err(reason) => FsymVerdict::Unknown { reason },
        };
        self.record_verdict(node, inst_index, kind, message, verdict, (None, None));
    }

    /// `Ok` when the bytes `needed` covers, of the `needed.size()` bytes at
    /// `pointer`, are proven initialized.
    fn init_state(
        &self,
        pointer: Option<&PointerFacts>,
        needed: Option<&ByteCoverage>,
    ) -> Result<(), String> {
        let pointer = pointer.ok_or("pointer facts unavailable; the bytes read are unknown")?;
        let Some(object) = pointer.object else {
            return Err(format!(
                "{}; the contents of its object are unknown",
                untracked_reason(pointer)
            ));
        };
        if let Some(call) = self.havocked.get(&object.id) {
            return Err(format!(
                "call `{call}` could reach this object and may have overwritten it"
            ));
        }
        let bits = self.init.get(&object.id).ok_or(
            "the object's initialization is not tracked (size not constant or over 4096 bytes)",
        )?;
        let needed = needed.ok_or("size of the accessed type is unknown")?;
        match pointer.byte_offset.as_ref().and_then(eval_concrete_u64) {
            Some(offset) => {
                let end = offset
                    .checked_add(needed.size())
                    .filter(|end| *end <= bits.len() as u64)
                    .ok_or("the bytes read lie outside the object")?;
                let read = &bits[offset as usize..end as usize];
                if read
                    .iter()
                    .zip(0u64..)
                    .all(|(bit, byte)| *bit || !needed.contains(byte))
                {
                    Ok(())
                } else {
                    Err("may read bytes not written on this path (poison), or padding a whole-aggregate store left uninitialized".to_string())
                }
            }
            None if bits.iter().all(|bit| *bit) => Ok(()),
            None => Err(
                "offset is not a constant and the object is not fully initialized on this path"
                    .to_string(),
            ),
        }
    }

    /// A write of `count` bytes (all of them initialized) at `ptr`: marks them
    /// in its tracked object when the offset and count are constants. An
    /// inexact write marks nothing, which only ever under-approximates what
    /// is initialized.
    fn mark_init(&mut self, ptr: ValueId, count: Option<u64>) {
        let Some((id, offset)) = self.tracked_offset(ptr) else {
            return;
        };
        let (Some(offset), Some(count)) = (offset, count) else {
            return;
        };
        if let Some(bits) = self.init.get_mut(&id) {
            let end = offset.saturating_add(count).min(bits.len() as u64);
            for bit in bits
                .iter_mut()
                .take(end as usize)
                .skip(offset.min(end) as usize)
            {
                *bit = true;
            }
        }
    }

    /// A copy of `count` bytes from `src` to `dst`: each destination byte
    /// takes the source byte's initialization. When the ranges or the source
    /// are not exact, every destination byte the copy may touch is marked
    /// uninitialized (the copy can move poison).
    fn copy_init(&mut self, dst: ValueId, src: ValueId, count: Option<u64>) {
        let Some((dst_id, dst_offset)) = self.tracked_offset(dst) else {
            return;
        };
        let source_bits =
            self.tracked_offset(src)
                .zip(count)
                .and_then(|((src_id, src_offset), count)| {
                    let src_offset = src_offset?;
                    let bits = self.init.get(&src_id)?;
                    let end = src_offset.checked_add(count)?;
                    (end <= bits.len() as u64)
                        .then(|| bits[src_offset as usize..end as usize].to_vec())
                });
        let Some(bits) = self.init.get_mut(&dst_id) else {
            return;
        };
        match (dst_offset, source_bits) {
            (Some(dst_offset), Some(source_bits)) => {
                for (index, bit) in source_bits.into_iter().enumerate() {
                    if let Some(slot) = usize::try_from(dst_offset)
                        .ok()
                        .and_then(|offset| offset.checked_add(index))
                        .and_then(|position| bits.get_mut(position))
                    {
                        *slot = bit;
                    }
                }
            }
            (Some(dst_offset), None) if count.is_some() => {
                let end = dst_offset
                    .saturating_add(count.unwrap_or(0))
                    .min(bits.len() as u64);
                for bit in bits
                    .iter_mut()
                    .take(end as usize)
                    .skip(dst_offset.min(end) as usize)
                {
                    *bit = false;
                }
            }
            _ => bits.iter_mut().for_each(|bit| *bit = false),
        }
    }

    /// The tracked object `ptr` points into and its constant offset, if any.
    fn tracked_offset(&self, ptr: ValueId) -> Option<(u64, Option<u64>)> {
        let pointer = self.values.get(&ptr)?.pointer.as_ref()?;
        let object = pointer.object?;
        Some((
            object.id,
            pointer.byte_offset.as_ref().and_then(eval_concrete_u64),
        ))
    }

    /// `Dealloc`: the pointer must be the base of a live heap allocation
    /// (`InvalidFree`), and not one already freed (`UseAfterFree`, the double
    /// free). Decidable misuses are diagnostics; everything else an Unknown.
    fn check_dealloc(&mut self, node: &InstrNode, inst_index: usize, ptr: ValueId) {
        let message = "invalid free";
        let invalid = FsymTrustIrDiagnosticKind::InvalidFree;
        let unknown = |reason: String| FsymVerdict::Unknown { reason };
        let ub = || FsymVerdict::Ub {
            witness: HashMap::new(),
        };
        let pointer = self
            .values
            .get(&ptr)
            .and_then(|facts| facts.pointer.clone());
        let object = pointer.as_ref().and_then(|pointer| pointer.object);
        let mut verdict = match (&pointer, object) {
            (None, _) => unknown(
                "pointer facts unavailable; cannot establish it is the base of a live heap allocation"
                    .to_string(),
            ),
            (Some(_), Some(object)) => match object.kind {
                // trust-cg-lower refuses a Dealloc of an Alloca, and a
                // machine free of a stack address is UB. (trust-ir's
                // reference interpreter is origin-permissive here — the
                // ub-numerics-policy engine-scope note.)
                ObjectKind::Stack => ub(),
                // A reference-counted cell is released by `Release`, never by
                // `Dealloc`: the reference interpreter raises UB for it at
                // any offset (`MemoryState::dealloc`, checked after the base
                // and liveness), and so does Lean's `semDealloc` for a
                // scalar-typed cell.
                ObjectKind::RcHeap => ub(),
                ObjectKind::Heap => match pointer
                    .as_ref()
                    .and_then(|pointer| pointer.byte_offset.as_ref())
                    .map(eval_concrete_u64)
                {
                    Some(Some(0)) => FsymVerdict::Safe,
                    Some(Some(_)) => ub(),
                    _ => unknown(
                        "offset from the allocation base is not modeled; cannot prove Dealloc receives the base"
                            .to_string(),
                    ),
                },
            },
            (Some(pointer), None) => {
                if pointer.addr.as_ref().and_then(eval_concrete_u64) == Some(0) {
                    ub()
                } else {
                    unknown(format!(
                        "{}; cannot establish it is the base of a live heap allocation",
                        untracked_reason(pointer)
                    ))
                }
            }
        };
        // Freeing an allocation under a live borrow is UB (trust-ir SPEC
        // "Freeing an allocation under a live borrow is undefined
        // behaviour"; the reference interpreter's `dealloc` raises it since
        // c06a487f). fsym does not track borrow counts, so a free on a path
        // that borrowed, or of an object a call on the path could reach (the
        // callee may have borrowed it and not ended the borrow), is never
        // proven.
        if let Some(borrow) = &self.borrow_seen
            && matches!(verdict, FsymVerdict::Safe)
        {
            verdict = unknown(format!(
                "freed on a path that borrowed at {borrow}; trust-ir forbids freeing a borrowed allocation and fsym does not track borrow permissions"
            ));
        }
        if let Some(call) = object.and_then(|object| self.havocked.get(&object.id))
            && matches!(verdict, FsymVerdict::Safe)
        {
            verdict = unknown(format!(
                "call `{call}` could reach this object and may have left a borrow of it live; trust-ir forbids freeing a borrowed allocation and fsym does not track borrow permissions across calls"
            ));
        }
        self.record_verdict(node, inst_index, invalid, message, verdict, (None, None));

        // The double free, through the lifetime stream. A free of an
        // untracked pointer may free anything an address escaped for.
        self.check_lifetime(node, inst_index, ptr, UafEventKind::Free, true);
        if object.is_none() && self.untracked_free.is_none() {
            self.untracked_free = Some(self.label(inst_index, "Dealloc"));
        }
    }

    /// An `unreachable` terminator on a walked path: UB whenever it is
    /// reached. After a call it is reached only if the call returns, which
    /// the scanner does not model — an Unknown.
    fn check_unreachable(&mut self, node: &InstrNode, inst_index: usize) {
        let message = "`unreachable` reached";
        let verdict = if let Some(call) = &self.passed_call {
            FsymVerdict::Unknown {
                reason: format!(
                    "reached unless the earlier call to `{call}` does not return; fsym does not model whether a callee returns"
                ),
            }
        } else {
            let empty_env = HashMap::new();
            let candidates: &[HashMap<String, u64>] = if self.ctx.witness_candidates.is_empty() {
                std::slice::from_ref(&empty_env)
            } else {
                self.ctx.witness_candidates.as_slice()
            };
            candidates
                .iter()
                .find(|env| guards_hold(&self.ctx.guards, env))
                .map_or_else(
                    || FsymVerdict::Unknown {
                        reason:
                            "reached whenever the path guards hold; not decided by the evaluator"
                                .to_string(),
                    },
                    |env| FsymVerdict::Ub {
                        witness: env.clone(),
                    },
                )
        };
        let solver = self
            .passed_call
            .is_none()
            .then_some(FsymTrustIrSolverObligation::Reachable);
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::UnreachableReached,
            message,
            verdict,
            (Some("true".to_string()), solver),
        );
    }

    fn check_uaf_event(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        ptr: ValueId,
        kind: UafEventKind,
    ) {
        if self.uaf_reported {
            // Accounted by the use-after-free already reported on this path
            // (a definite one: `uaf_reported` is never set past an unmodeled
            // branch).
            self.covered
                .insert((inst_index, FsymTrustIrDiagnosticKind::UseAfterFree));
            return;
        }
        let Some(object) = self
            .values
            .get(&ptr)
            .and_then(|facts| facts.pointer.as_ref())
            .and_then(|pointer| pointer.object)
        else {
            self.record_unaccounted_deref(
                node,
                inst_index,
                FsymTrustIrDiagnosticKind::UseAfterFree,
                "use after free or double free",
                "the pointer's object is not tracked; its lifetime is unknown",
            );
            return;
        };

        let object = SmtExpr::bv_const(object.id, 64);
        let candidate_expression = object.to_string();
        self.uaf_events.push(UafEvent {
            label: self.label(inst_index, "lifetime"),
            kind,
            object,
        });

        let verdict = check_uaf_ub(&self.uaf_events, &self.ctx);
        // Only a REPORTED use-after-free silences the later ones; past an
        // unmodeled branch it is recorded as an Unknown (`path_verdict`).
        if matches!(verdict, FsymVerdict::Ub { .. }) && self.unmodeled_branch.is_none() {
            self.uaf_reported = true;
        }
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::UseAfterFree,
            "use after free or double free",
            verdict,
            (Some(candidate_expression), None),
        );
    }

    /// The natural alignment (bytes) of `ty`: the reference interpreter's
    /// (`fsym_layout`).
    fn natural_align(&self, ty: &Ty) -> Option<u64> {
        FsymLayout::new(self.module).align(ty).ok()
    }

    /// The modeled bit width of an integer type: its fixed width, or the
    /// module's pointer width for `Usize` / `Isize`.
    ///
    /// `None` for a vector: its operations are lane-wise, and the scanner's
    /// single bit-vector would carry and compare across lanes.
    fn int_width(&self, ty: &Ty) -> Option<u32> {
        match ty {
            Ty::Usize | Ty::Isize => self.target.pointer_bits,
            Ty::Vector(..) => None,
            ty => ty.bit_width(),
        }
    }

    /// Record the arithmetic-UB verdict of an operation with a UB side
    /// condition. EVERY such site records one (it is enumerated by
    /// `reachable_obligation_sites`): a width or operand the scanner cannot
    /// model is an Unknown by name, never a silent pass.
    fn check_arithmetic(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        op: BinOp,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) {
        let Some(kind) = arith_ub_kind(op, ty) else {
            return;
        };
        let message = format!("arithmetic UB in `{op}`");
        let Some(width) = self.int_width(ty).filter(|width| (1..=64).contains(width)) else {
            self.record_unaccounted_deref(
                node,
                inst_index,
                FsymTrustIrDiagnosticKind::Arithmetic,
                message,
                format!("{ty:?} arithmetic is outside the scanner's 1..=64-bit model"),
            );
            return;
        };
        let operand = |value: ValueId| {
            self.values
                .get(&value)
                .and_then(|facts| facts.expr.clone())
                .filter(|expr| expr.try_bv_width().ok() == Some(width))
        };
        // A shift's side condition reads only the amount: an unmodeled value
        // shifted by a constant in range is safe.
        let lhs = match (operand(lhs), kind) {
            (None, ArithUbKind::ShiftAmount) => Some(SmtExpr::bv_const(0, width)),
            (lhs, _) => lhs,
        };
        let (Some(lhs), Some(rhs)) = (lhs, operand(rhs)) else {
            self.record_unaccounted_deref(
                node,
                inst_index,
                FsymTrustIrDiagnosticKind::Arithmetic,
                message,
                "operand value is not modeled; cannot prove the side condition",
            );
            return;
        };

        let candidate_expression = format!("{op} side condition: {lhs}, {rhs}");
        let solver_obligation = FsymTrustIrSolverObligation::Arithmetic {
            kind,
            lhs: lhs.clone(),
            rhs: Some(rhs.clone()),
            width,
        };
        let verdict = check_arith_ub(
            &ArithOp {
                label: self.label(inst_index, op),
                kind,
                lhs,
                rhs,
                width,
            },
            &self.ctx,
        );
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::Arithmetic,
            message,
            verdict,
            (Some(candidate_expression), Some(solver_obligation)),
        );
    }

    fn check_unary(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        op: UnOp,
        ty: &Ty,
        operand: ValueId,
    ) {
        if !unop_has_arith_ub(op, ty) {
            return;
        }
        let Some(width) = self.int_width(ty).filter(|width| (1..=64).contains(width)) else {
            self.record_unaccounted_deref(
                node,
                inst_index,
                FsymTrustIrDiagnosticKind::Arithmetic,
                "arithmetic UB in `neg`",
                format!("{ty:?} arithmetic is outside the scanner's 1..=64-bit model"),
            );
            return;
        };
        let Some(lhs) = self
            .values
            .get(&operand)
            .and_then(|facts| facts.expr.clone())
            .filter(|expr| expr.try_bv_width().ok() == Some(width))
        else {
            self.record_unaccounted_deref(
                node,
                inst_index,
                FsymTrustIrDiagnosticKind::Arithmetic,
                "arithmetic UB in `neg`",
                "operand value is not modeled; cannot prove the side condition",
            );
            return;
        };

        let candidate_expression = format!("neg side condition: {lhs}");
        let solver_obligation = FsymTrustIrSolverObligation::Arithmetic {
            kind: ArithUbKind::Sneg,
            lhs: lhs.clone(),
            rhs: None,
            width,
        };
        let verdict = check_arith_ub(
            &ArithOp {
                label: self.label(inst_index, op),
                kind: ArithUbKind::Sneg,
                lhs,
                rhs: SmtExpr::bv_const(0, width),
                width,
            },
            &self.ctx,
        );
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::Arithmetic,
            "arithmetic UB in `neg`",
            verdict,
            (Some(candidate_expression), Some(solver_obligation)),
        );
    }

    /// The verdict this path may claim. Past an unmodeled branch
    /// (`unmodeled_branch`) the path is not known to be reachable, so a
    /// concrete UB witness proves only "UB if reached": it is reported as an
    /// Unknown naming that branch, exactly the verdict a symbolic branch
    /// condition yields.
    ///
    /// An Unknown there names the branch too: its solver candidate is
    /// withheld (`record_verdict`), so it is not an escalatable obligation.
    fn path_verdict(&self, verdict: FsymVerdict) -> FsymVerdict {
        let Some(branch) = &self.unmodeled_branch else {
            return verdict;
        };
        match verdict {
            FsymVerdict::Ub { .. } => FsymVerdict::Unknown {
                reason: format!(
                    "UB whenever this site is reached, but the path passes the unmodeled {branch}; reachability is not established"
                ),
            },
            FsymVerdict::Unknown { reason } => FsymVerdict::Unknown {
                reason: format!(
                    "{reason}; the path passes the unmodeled {branch}, so no solver escalation"
                ),
            },
            FsymVerdict::Safe => FsymVerdict::Safe,
        }
    }

    fn record_verdict(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        kind: FsymTrustIrDiagnosticKind,
        message: impl Into<String>,
        verdict: FsymVerdict,
        evidence: VerdictEvidence,
    ) {
        let (candidate_expression, solver_obligation) = evidence;
        let message = message.into();
        let verdict = self.path_verdict(verdict);
        // A solver model past an unmodeled branch could only choose that
        // branch's outcome as if it were a free input: withhold escalation.
        let solver_obligation = solver_obligation.filter(|_| self.unmodeled_branch.is_none());
        // Deref-coverage accounting: this (block, inst_index) site is now
        // discharged by a verdict. `Safe` is a justified pass (a dominating
        // not-null/in-bounds proof, an annotation, or a concrete-nonzero
        // address), `Ub` is a concrete diagnostic, `Unknown` is a recorded
        // solver candidate. All three count as accounted; the only thing the
        // invariant forbids is a reachable deref that records NONE of them.
        self.covered.insert((inst_index, kind));
        match verdict {
            FsymVerdict::Safe => {}
            FsymVerdict::Ub { witness } => {
                let mut witness: Vec<(String, u64)> = witness.into_iter().collect();
                witness.sort_by(|a, b| a.0.cmp(&b.0));
                self.diagnostics.push(FsymTrustIrDiagnostic {
                    kind,
                    module: self.module.name.clone(),
                    function: self.function.name.clone(),
                    block: self.block.id.index(),
                    inst_index,
                    span: node.span,
                    message,
                    witness,
                });
            }
            FsymVerdict::Unknown { reason } => {
                let path_guards = self.ctx.guards.iter().map(ToString::to_string).collect();
                let solver_candidate =
                    solver_obligation.map(|obligation| FsymTrustIrSolverCandidate {
                        path_guards: self.ctx.guards.clone(),
                        obligation,
                    });
                self.unknown_obligations.push(FsymTrustIrUnknown {
                    kind,
                    label: self.label(inst_index, &message),
                    module: self.module.name.clone(),
                    function: self.function.name.clone(),
                    block: self.block.id.index(),
                    inst_index,
                    reason,
                    path_guards,
                    candidate_expression,
                    solver_candidate,
                });
            }
        }
    }

    /// Record a reachable deref that the scanner cannot model (no pointer
    /// facts / size / offset) as a fail-closed `Unknown` obligation.
    ///
    /// This is the structural complement of the deref-coverage invariant: the
    /// absence of a model must route through `record_verdict` (as Unknown, a
    /// recorded solver candidate) rather than bypass it via an early return.
    /// That guarantees no reachable deref is ever an implicit pass, and that
    /// the site is marked covered so the invariant is satisfied honestly
    /// rather than by suppression.
    fn record_unaccounted_deref(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        kind: FsymTrustIrDiagnosticKind,
        message: impl Into<String>,
        reason: impl Into<String>,
    ) {
        self.record_verdict(
            node,
            inst_index,
            kind,
            message,
            FsymVerdict::Unknown {
                reason: reason.into(),
            },
            (None, None),
        );
    }

    fn set_closure_captures(&mut self, node: &InstrNode, captures: Option<Vec<ValueFacts>>) {
        if let Some(result) = node.results.first()
            && let Some(facts) = self.values.get_mut(result)
        {
            facts.closure_captures = captures;
        }
    }

    fn define_value(
        &mut self,
        node: &InstrNode,
        ty: Ty,
        expr: Option<SmtExpr>,
        pointer: Option<PointerFacts>,
    ) {
        if let Some(result) = node.results.first().copied() {
            self.values.insert(
                result,
                ValueFacts {
                    ty,
                    expr,
                    pointer,
                    variant: None,
                    int_as_float: None,
                    closure_captures: None,
                },
            );
        }
    }

    fn define_overflow(
        &mut self,
        node: &InstrNode,
        op: OverflowOp,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) {
        let result_expr = match op {
            OverflowOp::AddOverflow => self.binop_expr(BinOp::Add, lhs, rhs),
            OverflowOp::SubOverflow => self.binop_expr(BinOp::Sub, lhs, rhs),
            OverflowOp::MulOverflow => self.binop_expr(BinOp::Mul, lhs, rhs),
        };

        if let Some(result) = node.results.first().copied() {
            self.values.insert(
                result,
                ValueFacts {
                    ty: ty.clone(),
                    expr: result_expr,
                    pointer: None,
                    variant: None,
                    int_as_float: None,
                    closure_captures: None,
                },
            );
        }
        if let Some(flag) = node.results.get(1).copied() {
            self.values.insert(
                flag,
                ValueFacts {
                    ty: Ty::Bool,
                    expr: None,
                    pointer: None,
                    variant: None,
                    int_as_float: None,
                    closure_captures: None,
                },
            );
        }
    }

    fn binop_expr(&self, op: BinOp, lhs: ValueId, rhs: ValueId) -> Option<SmtExpr> {
        let lhs = self.values.get(&lhs)?.expr.clone()?;
        let rhs = self.values.get(&rhs)?.expr.clone()?;
        let width = same_bv_width(&lhs, &rhs)?;
        Some(match op {
            BinOp::Add => lhs.bvadd(rhs),
            BinOp::Sub => lhs.bvsub(rhs),
            BinOp::Mul => lhs.bvmul(rhs),
            BinOp::UDiv => lhs.bvudiv(rhs),
            BinOp::SDiv => lhs.bvsdiv(rhs),
            BinOp::URem => lhs.bvurem(rhs),
            BinOp::And => lhs.bvand(rhs),
            BinOp::Or => lhs.bvor(rhs),
            BinOp::Xor => lhs.bvxor(rhs),
            // An out-of-range amount is UB (`ShiftAmount`), not a value: the
            // result is modeled only for a constant amount below the width,
            // never folded (SMT `bvshl` would give 0; AArch64 masks).
            BinOp::Shl | BinOp::LShr | BinOp::AShr => {
                let amount = eval_concrete_u64(&rhs)?;
                if u128::from(amount) >= u128::from(width) {
                    return None;
                }
                match op {
                    BinOp::Shl => lhs.bvshl(rhs),
                    BinOp::LShr => lhs.bvlshr(rhs),
                    _ => lhs.bvashr(rhs),
                }
            }
            // Trust: the BOOLEAN connectives (trust-ir 4b06918). Exact rather than
            // approximate: trust-ir's validator admits BAnd/BOr/BXor on `Bool` only,
            // so the carrier is the 1-bit bitvector, on which the bitwise BV ops ARE
            // the logical ones -- the same identification `AYBridge.lean`'s
            // `encodeBinOp` makes for these opcodes.
            BinOp::BAnd => lhs.bvand(rhs),
            BinOp::BOr => lhs.bvor(rhs),
            BinOp::BXor => lhs.bvxor(rhs),
            // trust-ir WS3.20 rotates are TOTAL (the amount is reduced modulo
            // the width): with `a = rhs mod w`,
            // `rotl = (lhs << a) | (lhs >>u (w - a))`. At `a = 0` the second
            // shift is by exactly `w`, which leaves `lhs` under either a
            // saturating or a masking shift reading.
            BinOp::RotL | BinOp::RotR => {
                let modulus = SmtExpr::bv_const(u64::from(width), width);
                let toward = rhs.bvurem(modulus.clone());
                let back = modulus.bvsub(toward.clone());
                if op == BinOp::RotL {
                    lhs.clone().bvshl(toward).bvor(lhs.bvlshr(back))
                } else {
                    lhs.clone().bvlshr(toward).bvor(lhs.bvshl(back))
                }
            }
            BinOp::SRem
            | BinOp::FAdd
            | BinOp::FSub
            | BinOp::FMul
            | BinOp::FDiv
            | BinOp::FRem
            | BinOp::FMin
            | BinOp::FMax
            | BinOp::FCopySign => {
                return None;
            }
        })
    }

    fn unop_expr(&self, op: UnOp, operand: ValueId) -> Option<SmtExpr> {
        let operand = self.values.get(&operand)?.expr.clone()?;
        Some(match op {
            UnOp::Neg => operand.bvneg(),
            // Left unmodeled: a use of the result sees no expression, which
            // keeps any obligation that depends on it Unknown.
            UnOp::Not
            | UnOp::FNeg
            | UnOp::FAbs
            | UnOp::FSqrt
            | UnOp::FFloor
            | UnOp::FCeil
            | UnOp::FTrunc
            | UnOp::CtPop
            | UnOp::CtLz
            | UnOp::CtTz
            | UnOp::BSwap
            | UnOp::BitReverse => return None,
        })
    }

    fn icmp_expr(&self, op: ICmpOp, lhs: ValueId, rhs: ValueId) -> Option<SmtExpr> {
        let lhs = self.values.get(&lhs)?.expr.clone()?;
        let rhs = self.values.get(&rhs)?.expr.clone()?;
        same_bv_width(&lhs, &rhs)?;
        Some(match op {
            ICmpOp::Eq => lhs.eq_expr(rhs),
            ICmpOp::Ne => lhs.eq_expr(rhs).not_expr(),
            ICmpOp::Ult => lhs.bvult(rhs),
            ICmpOp::Ule => lhs.bvule(rhs),
            ICmpOp::Ugt => lhs.bvugt(rhs),
            ICmpOp::Uge => lhs.bvuge(rhs),
            ICmpOp::Slt => lhs.bvslt(rhs),
            ICmpOp::Sle => lhs.bvsle(rhs),
            ICmpOp::Sgt => lhs.bvsgt(rhs),
            ICmpOp::Sge => lhs.bvsge(rhs),
        })
    }

    /// A `Select`'s value. Its condition is made Bool-sorted; Bool arms
    /// become a Boolean formula rather than an `ite` over Bools (whose
    /// `SmtExpr::sort` would ask a Bool for a bit width); arms of different
    /// sorts are unmodeled.
    fn select_expr(&self, cond: ValueId, then_val: ValueId, else_val: ValueId) -> Option<SmtExpr> {
        let cond = self.values.get(&cond)?.expr.clone()?;
        let then_expr = self.values.get(&then_val)?.expr.clone()?;
        let else_expr = self.values.get(&else_val)?.expr.clone()?;
        let cond = match expr_sort(&cond)? {
            SmtSort::Bool => cond,
            SmtSort::BitVec(1) => cond.eq_expr(SmtExpr::bv_const(1, 1)),
            _ => return None,
        };
        match (expr_sort(&then_expr)?, expr_sort(&else_expr)?) {
            (SmtSort::Bool, SmtSort::Bool) => Some(
                cond.clone()
                    .and_expr(then_expr)
                    .or_expr(cond.not_expr().and_expr(else_expr)),
            ),
            (then_sort, else_sort) if then_sort == else_sort => {
                Some(SmtExpr::ite(cond, then_expr, else_expr))
            }
            _ => None,
        }
    }

    /// The byte size of `ty`: the reference interpreter's (`fsym_layout`).
    fn type_size_bytes(&self, ty: &Ty) -> Option<u64> {
        FsymLayout::new(self.module).size(ty).ok()
    }

    fn label(&self, inst_index: usize, subject: impl fmt::Display) -> String {
        format!(
            "{} bb{} inst{} {}",
            self.function.name,
            self.block.id.index(),
            inst_index,
            subject
        )
    }
}

fn parameter_facts(
    function: &Function,
    value: ValueId,
    ty: &Ty,
    pointer_bits: Option<u32>,
) -> ValueFacts {
    let expr = parameter_expr(function, value, ty, pointer_bits);
    // A parameter's address is a free input with no tracked provenance (the
    // caller's object is not one the scan created) — WHEN it has one: the
    // caller may hand a pointer lying where base + offset has no address.
    let pointer = if is_pointer_like_ty(ty) {
        expr.clone().map(|expr| PointerFacts {
            nameable: false,
            ..PointerFacts::untracked(Some(expr))
        })
    } else {
        None
    };

    ValueFacts {
        ty: ty.clone(),
        expr,
        pointer,
        variant: None,
        int_as_float: None,
        closure_captures: None,
    }
}

/// Width (bits) of the scanner's ABSTRACT pointer values.
///
/// A modeled pointer is a null-ness/object-identity value, not a target
/// address: `NullPtr` is 0, an `Alloca` is a nonzero object id, a parameter
/// is a free variable. The scanner builds every one of them — and every
/// null-dereference obligation (`check_null` `ptr_width: 64`) — at this one
/// width on every target. It is NOT the target pointer width: `Usize` /
/// `Isize` values are modeled at `ScanTarget::pointer_bits`
/// (`target_info.pointer_size`), and a pointer/integer cast is modeled only
/// where the two widths agree (`cast_expr`). Trust: this MUST match the
/// `ptr_width` constants below.
const FSYM_TRUST_IR_POINTER_BITS: u32 = 64;

/// True for every pointer-like Trust IR type the scanner treats as a
/// dereferenceable pointer (bare `Ptr`, raw `*const`/`*mut`, Rust
/// `&`/`&mut`, `Rc`, and the data lane of a fat pointer `FatPtr`). A
/// null/bounds/UAF obligation rooted at a parameter of any of these types must
/// not be silently dropped.
///
/// `FatPtr` is included for type-set CONSISTENCY with `Ty::bit_width_with`,
/// which sizes a fat pointer at `2 * pointer_bits` (128 on a 64-bit target):
/// without this entry a `FatPtr` param got neither a symbolic expr (the 128-bit
/// width tripped the `width > 64` guard in `parameter_expr`) NOR `PointerFacts`,
/// so its derefs routed to unaccounted/unknown rather than analyzed. We model
/// the dereferenceable DATA-pointer lane of the fat pointer at the same 64-bit
/// `FSYM_TRUST_IR_POINTER_BITS` the rest of the scanner assumes (see
/// `parameter_expr`'s FatPtr arm); the 128-bit semantic width is unchanged
/// everywhere else. Keep this predicate and `parameter_expr` in lockstep so the
/// two can never drift again.
pub(crate) fn is_pointer_like_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::Rc(_)
            | Ty::FatPtr(_)
    )
}

fn parameter_expr(
    function: &Function,
    value: ValueId,
    ty: &Ty,
    pointer_bits: Option<u32>,
) -> Option<SmtExpr> {
    // v43: a nominal opaque runtime handle is NOT modeled. `bit_width_with`
    // resolves it to one pointer word, so without this it would become an
    // ordinary 64-bit bit-vector variable and the scanner could reason about
    // it structurally — compare two handles, relate one to an address — about
    // a value whose only guaranteed property is that a pinned runtime produced
    // it. Leaving it unmodeled is the conservative direction for a scanner: an
    // obligation that needs this value routes to unknown/unaccounted rather
    // than being discharged against an abstraction nothing justifies.
    if ty.contains_handle() {
        return None;
    }
    // A fat pointer is two pointer-sized lanes (`bit_width_with` sizes it at
    // `2 * pointer_bits` = 128 on a 64-bit target). The dereferenceable lane is
    // the DATA pointer; model it at the scanner's thin-pointer width (64) so a
    // FatPtr param gets a symbolic address (and thus PointerFacts) at the same
    // `ptr_width: 64` the deref obligations assume — rather than vanishing under
    // the `width > 64` guard. We do NOT relax that guard globally; this is a
    // FatPtr-specific special case to the 64-bit data lane.
    if matches!(ty, Ty::FatPtr(_)) {
        return Some(SmtExpr::var(
            format!("{}_arg{}", function.name, value.index()),
            FSYM_TRUST_IR_POINTER_BITS,
        ));
    }
    // Pointer-like types have a target-dependent width that `bit_width()`
    // leaves as `None`; resolve them at the scanner's abstract pointer width
    // so a pointer parameter gets a symbolic address (and thus PointerFacts)
    // instead of vanishing. `Usize` / `Isize` resolve at the TARGET pointer
    // width, and stay unmodeled when the module pins none.
    let width = if is_pointer_like_ty(ty) {
        FSYM_TRUST_IR_POINTER_BITS
    } else {
        match ty {
            Ty::Usize | Ty::Isize => pointer_bits?,
            ty => ty.bit_width_with(pointer_bits.unwrap_or(FSYM_TRUST_IR_POINTER_BITS))?,
        }
    };
    if width == 0 || width > 64 {
        return None;
    }
    Some(SmtExpr::var(
        format!("{}_arg{}", function.name, value.index()),
        width,
    ))
}

/// Structurally enumerate the reachable obligation sites in `block`.
///
/// Returns `(inst_index, opcode, kinds)` for every instruction the scanner is
/// responsible for accounting with verdicts: `kinds` lists EACH obligation
/// class the site owes a verdict for (`obligation_kinds`). This is the
/// *expected* set for the fail-closed coverage invariant in `run_block`: a
/// check that returns without recording its class's verdict — the historical
/// shape of every fail-open here — leaves a hole the invariant reports. Keep
/// this in lockstep with the dispatch in `visit_node`. The match is
/// exhaustive over `trust_ir::Inst` so a new obligation-carrying variant
/// cannot be left out silently.
///
/// Instructions past the terminator are unreachable within the block and are
/// not enumerated (the walk stops at the terminator too); an `unreachable`
/// terminator itself is a site.
fn reachable_obligation_sites(
    module: &Module,
    block: &Block,
) -> Vec<(usize, &'static str, Vec<FsymTrustIrDiagnosticKind>)> {
    let mut sites = Vec::new();
    for (inst_index, node) in block.body.iter().enumerate() {
        if node.is_terminator() {
            if matches!(node.inst, Inst::Unreachable) {
                sites.push((
                    inst_index,
                    "Unreachable",
                    vec![FsymTrustIrDiagnosticKind::UnreachableReached],
                ));
            }
            break;
        }
        if let Some((opcode, kinds)) = obligation_kinds(module, &node.inst) {
            sites.push((inst_index, opcode, kinds));
        }
    }
    sites
}

/// The opcode name of an instruction that carries obligations the scanner
/// must discharge, and the class of each, or `None`.
fn obligation_kinds(
    module: &Module,
    inst: &Inst,
) -> Option<(&'static str, Vec<FsymTrustIrDiagnosticKind>)> {
    use FsymTrustIrDiagnosticKind as K;
    let read = || {
        vec![
            K::NullDeref,
            K::OutOfBounds,
            K::UseAfterFree,
            K::Misaligned,
            K::Uninitialized,
        ]
    };
    let write = || vec![K::NullDeref, K::OutOfBounds, K::UseAfterFree, K::Misaligned];
    // Storing a value that holds a pointer exposes its address.
    let stored = |mut kinds: Vec<FsymTrustIrDiagnosticKind>, ty: &Ty| {
        if ty_may_hold_address(module, ty) {
            kinds.push(K::PointerArithmetic);
        }
        kinds
    };
    let bulk = |overlap_is_ub: bool| {
        let mut kinds = vec![K::NullDeref, K::OutOfBounds, K::UseAfterFree];
        if overlap_is_ub {
            kinds.push(K::Overlap);
        }
        kinds
    };
    match inst {
        Inst::Load { .. } => Some(("Load", read())),
        Inst::AtomicLoad { .. } => Some(("AtomicLoad", read())),
        Inst::Store { ty, .. } => Some(("Store", stored(write(), ty))),
        Inst::AtomicStore { ty, .. } => Some(("AtomicStore", stored(write(), ty))),
        Inst::AtomicRMW { ty, .. } => Some(("AtomicRMW", stored(read(), ty))),
        Inst::CmpXchg { ty, .. } => Some(("CmpXchg", stored(read(), ty))),
        Inst::MemCopy { overlap, .. } => Some(("MemCopy", bulk(!*overlap))),
        Inst::MemSet { .. } => Some(("MemSet", bulk(false))),
        Inst::Call { callee, args } => match classify_call(module, *callee, args.len()) {
            CallEffect::Bulk { symbol, kind } => Some((
                symbol,
                match kind {
                    BulkCallKind::Memset => bulk(false),
                    BulkCallKind::Memcpy => bulk(true),
                    BulkCallKind::Memmove => bulk(false),
                },
            )),
            CallEffect::ValueOnly
            | CallEffect::ModuleBody
            | CallEffect::External { .. }
            | CallEffect::Unresolved { .. }
            | CallEffect::Refused { .. } => Some(("Call", vec![K::UnsummarizedCall])),
        },
        Inst::BinOp { op, ty, .. } => {
            arith_ub_kind(*op, ty).map(|_| ("BinOp", vec![K::Arithmetic]))
        }
        Inst::UnOp { op, ty, .. } => {
            unop_has_arith_ub(*op, ty).then(|| ("UnOp", vec![K::Arithmetic]))
        }
        Inst::GEP { .. } => Some(("GEP", vec![K::NullDeref, K::PointerArithmetic])),
        Inst::Dealloc { .. } => Some(("Dealloc", vec![K::InvalidFree, K::UseAfterFree])),
        // Every allocation owes its count (when dynamic) and its PLACEMENT:
        // "base / next address overflow" can arise at any of them once a
        // placement of the run is unmodeled (`under_budget_premise`).
        Inst::Alloca { .. } => Some(("Alloca", vec![K::Arithmetic])),
        Inst::HeapAlloc { .. } => Some(("HeapAlloc", vec![K::Arithmetic])),
        // Materializing a module global places its storage (on first use)
        // and writes its initializer's image, addresses included.
        Inst::GlobalAddr { .. } => Some(("GlobalAddr", vec![K::Arithmetic, K::PointerArithmetic])),
        Inst::Const { .. } if materializes_global(inst) => {
            Some(("Const", vec![K::Arithmetic, K::PointerArithmetic]))
        }
        // A pointer/integer cast materializes or names an address.
        Inst::Cast { src_ty, dst_ty, .. }
            if is_pointer_like_ty(src_ty) != is_pointer_like_ty(dst_ty) =>
        {
            Some(("Cast", vec![K::PointerArithmetic]))
        }
        Inst::ICmp { ty: Ty::Ptr, .. } => Some(("ICmp", vec![K::PointerArithmetic])),
        // A raw float-to-integer conversion of NaN or an out-of-range value.
        Inst::Cast { op, .. } if float_to_int_has_ub(*op) => Some(("Cast", vec![K::Arithmetic])),
        // A borrow of a thin pointer dereferences it for the interpreter's
        // purposes: null and a pointer with no allocation provenance are UB.
        Inst::Borrow { .. } => Some(("Borrow", vec![K::NullDeref, K::OutOfBounds])),
        Inst::BorrowMut { .. } => Some(("BorrowMut", vec![K::NullDeref, K::OutOfBounds])),
        // Aggregate lanes and vector elements must exist in the value.
        Inst::ExtractField { .. } => Some(("ExtractField", vec![K::OutOfBounds])),
        Inst::InsertField { .. } => Some(("InsertField", vec![K::OutOfBounds])),
        Inst::ExtractElement { .. } => Some(("ExtractElement", vec![K::OutOfBounds])),
        Inst::InsertElement { .. } => Some(("InsertElement", vec![K::OutOfBounds])),
        // `EndBorrow` has no run-time effect (a Dealloc after a borrow is an
        // Unknown); `Retain` / `Release` / `IsUnique` are refused at admission.
        Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. }
        | Inst::Drop { .. } => None,
        // No obligation of their own: values, total arithmetic (`Overflow`
        // returns a flag), fences, and the constructs the admission gate
        // refuses. A count-less allocation has none either.
        Inst::Const { .. }
        | Inst::NullPtr
        | Inst::Copy { .. }
        | Inst::Cast { .. }
        | Inst::Overflow { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Select { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::Fence { .. }
        | Inst::CallIndirect { .. }
        | Inst::CallCannotUnwind { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        // v67: refused at admission (`unsupported_nonterminator_detail`).
        | Inst::BoxDeref { .. }
        | Inst::Undef { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::AssertInvoke { .. }
        | Inst::DropInvoke { .. }
        | Inst::InvokeIndirect { .. }
        | Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        | Inst::SeqMap { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::LandingPad { .. }
        | Inst::DialectOp(_)
        | Inst::MakeAggregate { .. }
        | Inst::MakeClosure { .. }
        | Inst::ArraySplat { .. } => None,
        Inst::TensorContract { .. }
        | Inst::TensorMap { .. }
        | Inst::TensorReduce { .. }
        | Inst::TensorView { .. }
        | Inst::TensorGather { .. }
        | Inst::TensorScatter { .. } => None,
        // Terminators end the walk before this is consulted.
        Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Return { .. }
        | Inst::Unreachable
        | Inst::CoroSuspend { .. }
        | Inst::Invoke { .. }
        | Inst::Resume { .. } => None,
    }
}

/// Every diagnostic kind fsym owes a verdict for at `inst` when it is
/// reached: what the per-block deref-coverage invariant (`run_block`)
/// enforces — a reached site that records no verdict of one of these kinds is
/// a coverage error. The admission gate checks the interpreter-derived UB map
/// against it (`fsym_ub_map::fsym_map_refusal`).
pub fn fsym_owed_kinds(module: &Module, inst: &Inst) -> Vec<FsymTrustIrDiagnosticKind> {
    match inst {
        Inst::Unreachable => vec![FsymTrustIrDiagnosticKind::UnreachableReached],
        inst => obligation_kinds(module, inst)
            .map(|(_, kinds)| kinds)
            .unwrap_or_default(),
    }
}

/// Bulk memory semantics trust-cg-lower gives a direct call by name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BulkCallKind {
    /// `(dst, value, len)`: writes `len` bytes at `dst`.
    Memset,
    /// `(dst, src, len)`: non-overlapping copy — overlapping ranges are UB.
    Memcpy,
    /// `(dst, src, len)`: copy that defines overlapping ranges.
    Memmove,
}

/// The EXACT callee symbols fsym checks as bulk memory accesses, exactly as
/// `Inst::MemSet` / `Inst::MemCopy` are checked: the C library routines and
/// the LLVM intrinsics trust-cg-llvm-import passes through (opaque-pointer
/// spelling, 32- and 64-bit lengths, and their `.inline` forms; the importer
/// strips the trailing `i1 <volatile>` flag, so every entry takes three
/// arguments). trust-cg-lower lowers a call of each to the matching
/// `Opcode::Memset` / `Memcpy` / `Memmove` when the callee is declared with
/// the prototype that name needs (the C library's for the plain names,
/// LLVM's for the intrinsics: `classify_adapter_direct_call`), and a call of
/// a plain name declared otherwise as an ordinary call; the names are pinned
/// by `bulk_memory_symbols_match_the_lowering`. A name the lowering treats as
/// bulk memory that is NOT listed here is refused by name at admission, never
/// checked as something it might not be.
const BULK_MEMORY_SYMBOLS: &[(&str, BulkCallKind)] = &[
    ("memset", BulkCallKind::Memset),
    ("memcpy", BulkCallKind::Memcpy),
    ("memmove", BulkCallKind::Memmove),
    ("llvm.memset.p0.i32", BulkCallKind::Memset),
    ("llvm.memset.p0.i64", BulkCallKind::Memset),
    ("llvm.memset.inline.p0.i32", BulkCallKind::Memset),
    ("llvm.memset.inline.p0.i64", BulkCallKind::Memset),
    ("llvm.memcpy.p0.p0.i32", BulkCallKind::Memcpy),
    ("llvm.memcpy.p0.p0.i64", BulkCallKind::Memcpy),
    ("llvm.memcpy.inline.p0.p0.i32", BulkCallKind::Memcpy),
    ("llvm.memcpy.inline.p0.p0.i64", BulkCallKind::Memcpy),
    ("llvm.memmove.p0.p0.i32", BulkCallKind::Memmove),
    ("llvm.memmove.p0.p0.i64", BulkCallKind::Memmove),
];

/// True for a direct call the scanner checks as a bulk memory access (a
/// `BULK_MEMORY_SYMBOLS` callee, `classify_call`), not as a callee.
pub(crate) fn is_bulk_memory_call(module: &Module, inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Call { callee, args }
            if matches!(classify_call(module, *callee, args.len()), CallEffect::Bulk { .. })
    )
}

fn bulk_memory_symbol(name: &str) -> Option<(&'static str, BulkCallKind)> {
    BULK_MEMORY_SYMBOLS
        .iter()
        .find(|(symbol, _)| *symbol == name)
        .copied()
}

/// What a direct `Call` means to the scanner.
#[derive(Debug, Clone, PartialEq, Eq)]
enum CallEffect {
    /// A bulk memory access by `(dst, value | src, len)`, checked by
    /// `check_bulk_memory` exactly like `MemSet` / `MemCopy`.
    Bulk {
        symbol: &'static str,
        kind: BulkCallKind,
    },
    /// A value-only intrinsic the lowering replaces (`bitreverse`,
    /// `objectsize`, `fma`): no memory effect.
    ValueOnly,
    /// A callee the link binds to its body in this module (`External` /
    /// `Internal` / `Private`). Each access it makes is an obligation of its
    /// own scan in the same report — unless the scanner refuses to scan it
    /// (`skipped_direct_callees`), which makes a pointer handed to it
    /// unsummarized.
    ModuleBody,
    /// A body-less callee, or one whose body the link may replace (`Weak`,
    /// `LinkOnce`, their ODR forms, `AvailableExternally`, `ExternalWeak`;
    /// see `callee_binds_to_module_body`): it may read, write or free through
    /// any pointer it is handed.
    External { replaceable: bool },
    /// The callee does not resolve in the module.
    Unresolved { reason: String },
    /// Refused at admission by name.
    Refused { detail: String },
}

/// True when a call to `function` binds to the body in this module: the link
/// cannot replace it. That is a bodied module-local function (trust-ir's
/// proved `Linkage::is_module_local`: `Internal` / `Private`) or a bodied
/// `External` one.
///
/// Deliberately narrower than trust-ir's `!Linkage::is_interposable()`, which
/// also counts `WeakOdr` / `LinkOnceOdr` / `AvailableExternally` as bound
/// under the one-definition-rule premise trust-ir discloses and does not
/// verify (every copy is the same definition). fsym does not take that
/// premise: the copy the link keeps may be another object's, and an
/// `AvailableExternally` body is never the one this object emits, so a call
/// to one is scanned as replaceable ([`CallEffect::External`]).
fn callee_binds_to_module_body(function: &Function) -> bool {
    function.has_body()
        && (function.linkage.is_module_local() || function.linkage == Linkage::External)
}

/// Classify a direct call by its callee's DECLARED name, linkage and
/// signature, mirroring trust-cg-lower's call lowering:
///
/// 1. A bodied `Internal` / `Private` callee binds to its own body even if
///    its name spells an intrinsic (the adapter's exact-module-binding rule).
/// 2. Otherwise the adapter's own reading of the call by its name AND
///    declared prototype (`classify_adapter_direct_call`) decides: a call it
///    lowers as bulk memory is a bulk memory access when its name is in
///    `BULK_MEMORY_SYMBOLS` and refused when not; a value-only intrinsic it
///    substitutes touches no memory; a call it refuses by name is refused;
///    and a library name declared with another prototype (`memset`
///    returning an integer) is an ordinary call, classified below.
/// 3. A callee with a body in this module (`External` / `Internal` /
///    `Private` — a definition the link cannot replace) is `ModuleBody`.
/// 4. Any other callee — body-less (an external import), or a body the link
///    may replace — is `External`: `visit_call` decides from the arguments
///    whether it is handed a pointer.
fn classify_call(module: &Module, callee: FuncId, arg_count: usize) -> CallEffect {
    let Some(function) = module.function_by_id(callee) else {
        return CallEffect::Unresolved {
            reason: format!(
                "callee f{} does not resolve in module `{}`; its memory effects are unknown",
                callee.index(),
                module.name
            ),
        };
    };
    let name = function.name.as_str();
    let has_body = function.has_body();
    let module_local = has_body && function.linkage.is_module_local();
    if !module_local {
        let Some(signature) = module.func_type(function.ty) else {
            return CallEffect::Unresolved {
                reason: format!(
                    "callee `{name}` names function type {} that module `{}` does not hold; its \
                     memory effects are unknown",
                    function.ty.index(),
                    module.name
                ),
            };
        };
        // The lowering's own decision, by name AND declared prototype: a
        // `memset` declared otherwise than C's is an ordinary external call
        // there, so it is one here too.
        match classify_adapter_direct_call(name, function, signature) {
            Err(refusal) => {
                return CallEffect::Refused {
                    detail: format!("trust-cg-lower refuses the call by name: {refusal}"),
                };
            }
            Ok(
                AdapterNamedCallSemantics::Memcpy
                | AdapterNamedCallSemantics::Memmove
                | AdapterNamedCallSemantics::Memset,
            ) => {
                let Some((symbol, kind)) = bulk_memory_symbol(name) else {
                    return CallEffect::Refused {
                        detail: format!(
                            "call to `{name}` is lowered as bulk memory by trust-cg-lower but is not one of the bulk-memory symbols fsym models"
                        ),
                    };
                };
                if arg_count != 3 {
                    return CallEffect::Refused {
                        detail: format!(
                            "call to bulk-memory symbol `{name}` passes {arg_count} argument(s); fsym models only its (dst, value|src, len) form"
                        ),
                    };
                }
                return CallEffect::Bulk { symbol, kind };
            }
            Ok(
                AdapterNamedCallSemantics::Bitreverse
                | AdapterNamedCallSemantics::Objectsize
                | AdapterNamedCallSemantics::Fma
                | AdapterNamedCallSemantics::PackedFma
                | AdapterNamedCallSemantics::Crc32,
            ) => return CallEffect::ValueOnly,
            Ok(AdapterNamedCallSemantics::Ordinary) => {}
        }
    }
    if callee_binds_to_module_body(function) {
        return CallEffect::ModuleBody;
    }
    CallEffect::External {
        replaceable: has_body,
    }
}

/// The symbols `constant` addresses (every `SymbolAddr` in it).
fn constant_symbols(constant: &Constant) -> Vec<&str> {
    let mut windows = Vec::new();
    constant_windows(constant, &mut windows);
    windows.into_iter().map(|(symbol, _)| symbol).collect()
}

/// Whether `inst` MATERIALIZES a module global when it runs: `GlobalAddr`,
/// or a `Const` whose value addresses a symbol (the interpreter's
/// `symbol_pointer` places the global it names). A global's first use
/// allocates and places its storage and writes its initializer.
pub(crate) fn materializes_global(inst: &Inst) -> bool {
    match inst {
        Inst::GlobalAddr { .. } => true,
        Inst::Const { value, .. } => !constant_symbols(value).is_empty(),
        _ => false,
    }
}

/// The module globals (by index) `inst` may materialize: the one it names,
/// and — transitively — every global a materialized global's initializer
/// addresses. A symbol naming no global, or several, is a type error to the
/// interpreter and places nothing.
fn materialized_globals(module: &Module, inst: &Inst) -> Vec<usize> {
    let by_symbol = |symbol: &str| {
        let mut named = module
            .globals
            .iter()
            .enumerate()
            .filter(|(_, global)| global.name == symbol);
        match (named.next(), named.next()) {
            (Some((index, _)), None) => Some(index),
            _ => None,
        }
    };
    let mut pending = Vec::new();
    match inst {
        Inst::GlobalAddr { global } => pending.push(global.index() as usize),
        Inst::Const { value, .. } => {
            pending.extend(constant_symbols(value).into_iter().filter_map(by_symbol));
        }
        _ => {}
    }
    let mut seen: Vec<usize> = Vec::new();
    while let Some(index) = pending.pop() {
        if seen.contains(&index) {
            continue;
        }
        seen.push(index);
        if let Some(init) = module
            .globals
            .get(index)
            .and_then(|global| global.initializer.as_ref())
        {
            pending.extend(constant_symbols(init).into_iter().filter_map(by_symbol));
        }
    }
    seen
}

/// Where a materialized global's initializer names a pointer one past the
/// end of a non-empty global — a `SymbolAddr` whose addend is the named
/// global's size (a zero-extent window; any other window that fits lies
/// inside it, one that does not is a type error) — or names a global fsym
/// cannot size: on a target whose address space a global may end with,
/// encoding that pointer may find no address ("Store: pointer address
/// overflow"). `None` when every such pointer is nameable.
fn initializer_end_pointer(module: &Module, globals: &[usize]) -> Option<String> {
    let layout = FsymLayout::new(module);
    for &index in globals {
        let Some(global) = module.globals.get(index) else {
            continue;
        };
        let Some(init) = &global.initializer else {
            continue;
        };
        let mut windows = Vec::new();
        constant_windows(init, &mut windows);
        for (symbol, addend) in windows {
            let mut named = module.globals.iter().filter(|g| g.name == symbol);
            let (Some(target), None) = (named.next(), named.next()) else {
                continue; // a type error to the interpreter, which places nothing
            };
            match (layout.size(&target.ty), u64::try_from(addend)) {
                (Ok(size), Ok(addend)) if addend == size && size > 0 => {
                    return Some(format!(
                        "the initializer of global `{}` points one past the end of the {size}-byte global `{symbol}`, which may end exactly at the end of the 32-bit address space: that pointer has no address to encode",
                        global.name
                    ));
                }
                // Inside the global, its base, or a window that does not fit
                // (a type error, not UB).
                (Ok(_), _) => {}
                (Err(_), _) => {
                    return Some(format!(
                        "the initializer of global `{}` points into global `{symbol}`, whose size fsym cannot lay out: its address may not be nameable",
                        global.name
                    ));
                }
            }
        }
    }
    None
}

/// Every `SymbolAddr { symbol, addend }` in `constant`.
fn constant_windows<'c>(constant: &'c Constant, out: &mut Vec<(&'c str, i64)>) {
    if let Constant::SymbolAddr { symbol, addend } = constant {
        out.push((symbol, *addend));
    }
    for child in constant.children() {
        constant_windows(child, out);
    }
}

/// Whether a value of `ty` encodes a pointer's ADDRESS when it is written to
/// memory (the reference interpreter's `encode_value` asks a pointer for its
/// address, "pointer address overflow" when `base + offset` overflows):
/// a pointer-like type, or an aggregate / vector with such a lane. An
/// unresolvable type counts (fail closed); a handle is never stored.
pub(crate) fn ty_may_hold_address(module: &Module, ty: &Ty) -> bool {
    fn walk(module: &Module, ty: &Ty, depth: usize) -> bool {
        if depth > 16 {
            return true;
        }
        if is_pointer_like_ty(ty) {
            return true;
        }
        if ty.is_integer() || ty.is_float() || matches!(ty, Ty::Bool | Ty::Char | Ty::Unit) {
            return false;
        }
        match ty {
            Ty::Vector(element, _) => walk(module, element, depth + 1),
            Ty::Tuple(lanes) => lanes.iter().any(|lane| walk(module, lane, depth + 1)),
            Ty::Array(element, _) => module
                .types
                .get(element.index() as usize)
                .is_none_or(|element| walk(module, element, depth + 1)),
            Ty::Struct(id) => module.struct_def(*id).is_none_or(|def| {
                def.fields
                    .iter()
                    .any(|field| walk(module, &field.ty, depth + 1))
            }),
            Ty::Enum(id) => module.enum_def(*id).is_none_or(|def| {
                def.variants.iter().any(|variant| {
                    variant
                        .fields
                        .iter()
                        .any(|field| walk(module, field, depth + 1))
                })
            }),
            _ => true,
        }
    }
    walk(module, ty, 0)
}

/// False only for types that cannot hold an address: scalars and vectors of
/// them. Pointers, references, fat pointers, handles, function values and
/// every aggregate may.
fn ty_may_carry_pointer(ty: &Ty) -> bool {
    match ty {
        Ty::Vector(element, _) => ty_may_carry_pointer(element),
        Ty::Bool | Ty::Char | Ty::Unit | Ty::Never => false,
        ty => !(ty.is_integer() || ty.is_float()),
    }
}

/// The casts trust-ir defines as UB on some operand values: the raw
/// float-to-integer conversions (NaN / out of range). Their saturating twins
/// (`FPToSISat` / `FPToUISat`) are total. Exhaustive over `CastOp` so a new
/// cast op cannot default to total unnoticed.
fn float_to_int_has_ub(op: CastOp) -> bool {
    match op {
        CastOp::FPToSI | CastOp::FPToUI => true,
        CastOp::Trunc
        | CastOp::ZExt
        | CastOp::SExt
        | CastOp::FPTrunc
        | CastOp::FPExt
        | CastOp::UIToFP
        | CastOp::SIToFP
        | CastOp::PtrToInt
        | CastOp::IntToPtr
        | CastOp::PtrToPtr
        | CastOp::Bitcast
        | CastOp::Transmute
        | CastOp::ReifyFnPointer
        | CastOp::FPToSISat
        | CastOp::FPToUISat => false,
    }
}

/// The arithmetic-UB obligation a binary operator carries, if any.
///
/// Exhaustive over `BinOp` (no wildcard) so a new operator with a UB side
/// condition cannot default to "total" unnoticed.
fn arith_ub_kind(op: BinOp, ty: &Ty) -> Option<ArithUbKind> {
    match op {
        BinOp::UDiv => Some(ArithUbKind::Udiv),
        BinOp::SDiv => Some(ArithUbKind::Sdiv),
        BinOp::URem => Some(ArithUbKind::Urem),
        BinOp::SRem => Some(ArithUbKind::Srem),
        BinOp::Add if ty.is_signed() => Some(ArithUbKind::Sadd),
        BinOp::Sub if ty.is_signed() => Some(ArithUbKind::Ssub),
        BinOp::Mul if ty.is_signed() => Some(ArithUbKind::Smul),
        // trust-ir's `ShiftInRange`: an amount not below the bit width is UB
        // (ub-numerics-policy section 1; NOT masked).
        BinOp::Shl | BinOp::LShr | BinOp::AShr => Some(ArithUbKind::ShiftAmount),
        // Unsigned add/sub/mul wrap. Bitwise and Boolean connectives are
        // total; trust-ir WS3.20 rotates reduce the amount modulo the width
        // and `FCopySign` is a sign-bit merge, both total; IEEE
        // floating-point operations have no UB.
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::And
        | BinOp::Or
        | BinOp::Xor
        | BinOp::BAnd
        | BinOp::BOr
        | BinOp::BXor
        | BinOp::RotL
        | BinOp::RotR
        | BinOp::FAdd
        | BinOp::FSub
        | BinOp::FMul
        | BinOp::FDiv
        | BinOp::FRem
        | BinOp::FMin
        | BinOp::FMax
        | BinOp::FCopySign => None,
    }
}

/// Whether a unary operator carries an arithmetic-UB obligation (signed
/// negation of the minimum value). Exhaustive over `UnOp`, like
/// `arith_ub_kind`.
fn unop_has_arith_ub(op: UnOp, ty: &Ty) -> bool {
    match op {
        UnOp::Neg => ty.is_signed(),
        // Bitwise and IEEE operations are total; trust-ir WS3.20 `ctlz` /
        // `cttz` are total (`0 -> width`), and byte swap / bit reverse are
        // permutations.
        UnOp::FNeg
        | UnOp::FAbs
        | UnOp::FSqrt
        | UnOp::FFloor
        | UnOp::FCeil
        | UnOp::FTrunc
        | UnOp::Not
        | UnOp::CtPop
        | UnOp::CtLz
        | UnOp::CtTz
        | UnOp::BSwap
        | UnOp::BitReverse => false,
    }
}

fn same_bv_width(lhs: &SmtExpr, rhs: &SmtExpr) -> Option<u32> {
    let lhs_width = lhs.try_bv_width().ok()?;
    (lhs_width == rhs.try_bv_width().ok()?).then_some(lhs_width)
}

fn bounds_solver_obligation(
    byte_offset: &SmtExpr,
    object_size_bytes: &SmtExpr,
    access_size_bytes: u64,
) -> Option<FsymTrustIrSolverObligation> {
    let width = same_bv_width(byte_offset, object_size_bytes)?;
    (1..=64)
        .contains(&width)
        .then(|| FsymTrustIrSolverObligation::OutOfBounds {
            byte_offset: byte_offset.clone(),
            object_size_bytes: object_size_bytes.clone(),
            access_size_bytes,
            width,
        })
}

fn switch_selector_width(ty: &Ty) -> Option<u32> {
    if !ty.is_integer() {
        return None;
    }
    let width = ty.bit_width()?;
    (1..=64).contains(&width).then_some(width)
}

fn switch_case_guard(selector: &SmtExpr, width: u32, value: &Constant) -> Option<SmtExpr> {
    let Constant::Int(value) = value else {
        return None;
    };
    Some(
        selector
            .clone()
            .eq_expr(SmtExpr::bv_const(*value as u64, width)),
    )
}

fn switch_default_guard(selector: &SmtExpr, width: u32, cases: &[SwitchCase]) -> Option<SmtExpr> {
    let mut guard = SmtExpr::bool_const(true);
    for case in cases {
        guard = guard.and_expr(switch_case_guard(selector, width, &case.value)?.not_expr());
    }
    Some(guard)
}

fn guard_is_concrete_false(guard: &SmtExpr) -> bool {
    let empty_env = HashMap::new();
    match guard.try_eval(&empty_env).ok() {
        Some(EvalResult::Bool(false)) => true,
        Some(EvalResult::Bv(0) | EvalResult::Bv128(0)) if guard.try_bv_width().ok() == Some(1) => {
            true
        }
        _ => false,
    }
}

fn constant_expr(ty: &Ty, value: &Constant, pointer_bits: Option<u32>) -> Option<SmtExpr> {
    match value {
        Constant::Ext(e) => e.unreachable(),
        Constant::Int(value) => {
            // `Usize` / `Isize` (the byte-count type of `MemCopy` / `MemSet`
            // in a target-pinned module) have the TARGET pointer width —
            // `target_info.pointer_size`, never an assumed 64: on a 32-bit
            // target `0xFFFF_FFFF + 1` wraps to 0. Unmodeled when the module
            // pins no width (such a function is refused before the walk).
            let width = match ty {
                Ty::Usize | Ty::Isize => pointer_bits?,
                _ => ty.bit_width()?,
            };
            if width == 0 || width > 64 {
                return None;
            }
            Some(SmtExpr::bv_const(*value as u64, width))
        }
        Constant::Bool(value) => Some(SmtExpr::bool_const(*value)),
        Constant::Float(value) => match ty {
            Ty::F32 => Some(SmtExpr::fp32_const(*value as f32)),
            Ty::F64 => Some(SmtExpr::fp64_const(*value)),
            _ => None,
        },
        // trust-ir v24 U128: the scanner's SMT lane is <= 64-bit (same gate
        // as the Int arm's `width > 64` bail) and a canonical U128 exceeds
        // i128::MAX by definition — no bit-vector to model; fail closed.
        Constant::U128(_)
        | Constant::Bytes { .. }
        | Constant::Aggregate(_)
        | Constant::Array(_)
        | Constant::Splat { .. }
        | Constant::Vector(_)
        | Constant::Sequence(_)
        | Constant::Set(_)
        | Constant::Record(_)
        | Constant::Closure { .. }
        | Constant::FnItem(_)
        | Constant::FnDef(_)
        // A symbol address has no concrete value until link time, so there is
        // no SMT bit-vector to model it as.
        | Constant::SymbolAddr { .. }
        | Constant::PhantomData => None,
        // A valid content-addressed weight has no bounded scalar model.
        Constant::TensorBlob { .. } => None,
        // v49: an unwritten lane is no value; there is nothing to model.
        Constant::Uninit => None,
    }
}

fn cast_expr(
    op: CastOp,
    src_ty: &Ty,
    dst_ty: &Ty,
    expr: SmtExpr,
    pointer_bits: Option<u32>,
) -> Option<SmtExpr> {
    // Resolve pointer-like widths at the fixed 64-bit pointer width (as the rest
    // of the scanner does, e.g. `parameter_expr`). `Ty::bit_width()` returns
    // `None` for pointers (target-dependent), which would otherwise make the
    // `IntToPtr`/`PtrToInt`/`Bitcast` arm below dead — leaving an int↔ptr cast
    // result with no SMT expr, hence a deref through it as an unaccounted
    // "pointer facts unavailable" Unknown instead of a candidate the solver can
    // discharge.
    // v43: NO cast is modeled with a handle on either side. Both are one
    // pointer word, so the `PtrToInt | IntToPtr | Bitcast if src_width ==
    // dst_width` arm below would otherwise model `Bitcast Ptr -> Handle` as the
    // IDENTITY — the scanner would carry a forged handle as if it were the
    // real one. trust-ir refuses that cast outright
    // (`LayoutError::OpaqueHandleCast`); this refuses to give it a meaning.
    if src_ty.contains_handle() || dst_ty.contains_handle() {
        return None;
    }
    // Pointer-like sides are the scanner's abstract 64-bit pointer values;
    // `Usize` / `Isize` sides are the target width. A pointer/integer cast is
    // the identity only on a target whose pointers ARE 64 bits: anywhere
    // else the abstract value is not the target address, so the result stays
    // unmodeled.
    // (A target-free module is lowered with 64-bit pointers, so a fixed
    // 64-bit integer side is exact there.)
    let pointer_integer_cast = is_pointer_like_ty(src_ty) != is_pointer_like_ty(dst_ty);
    if pointer_integer_cast && pointer_bits.is_some_and(|bits| bits != FSYM_TRUST_IR_POINTER_BITS) {
        return None;
    }
    let width = |ty: &Ty| match ty {
        Ty::Usize | Ty::Isize => pointer_bits,
        ty if is_pointer_like_ty(ty) => Some(FSYM_TRUST_IR_POINTER_BITS),
        ty => ty.bit_width_with(pointer_bits.unwrap_or(FSYM_TRUST_IR_POINTER_BITS)),
    };
    let src_width = width(src_ty)?;
    let dst_width = width(dst_ty)?;
    if src_width == 0 || dst_width == 0 || src_width > 64 || dst_width > 64 {
        return None;
    }
    // The operand as a bit-vector of the SOURCE width. A `Bool` (a
    // comparison result is Bool-sorted) is trust-ir's one-bit integer,
    // `false -> 0` / `true -> 1` (`CastOp` docs): `zext`/`sext` of it would
    // otherwise ask a Bool for a bit width (a panic, not a verdict). Any other
    // sort, or a width that disagrees with the source type, is unmodeled.
    let expr = match expr_sort(&expr)? {
        SmtSort::Bool if src_width == 1 => {
            SmtExpr::ite(expr, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
        }
        SmtSort::BitVec(width) if width == src_width => expr,
        _ => return None,
    };

    match op {
        CastOp::Trunc if dst_width <= src_width => Some(expr.extract(dst_width - 1, 0)),
        CastOp::ZExt if dst_width >= src_width => Some(expr.zero_ext(dst_width - src_width)),
        CastOp::SExt if dst_width >= src_width => Some(expr.sign_ext(dst_width - src_width)),
        CastOp::PtrToInt | CastOp::IntToPtr | CastOp::Bitcast if src_width == dst_width => {
            Some(expr)
        }
        _ => None,
    }
}

/// The sort of `expr`, or `None` when it is ill-sorted. Unlike
/// `SmtExpr::sort` it never panics: an `ite` is answered from its arms
/// (`sort` asks an `ite` for a bit width, which an `ite` over Bools lacks).
/// Every other expression `try_bv_width` refuses is one `sort` answers
/// without asking for a width (Boolean, floating-point, array, UF).
fn expr_sort(expr: &SmtExpr) -> Option<SmtSort> {
    if let Ok(width) = expr.try_bv_width() {
        return Some(SmtSort::BitVec(width));
    }
    match expr {
        SmtExpr::Ite {
            then_expr,
            else_expr,
            ..
        } => {
            let sort = expr_sort(then_expr)?;
            (expr_sort(else_expr)? == sort).then_some(sort)
        }
        _ => Some(expr.sort()),
    }
}

fn widen_index_to_i64(expr: SmtExpr, ty: &Ty) -> Option<SmtExpr> {
    let width = expr.try_bv_width().ok()?;
    match width {
        64 => Some(expr),
        1..=63 if ty.is_signed() => Some(expr.sign_ext(64 - width)),
        1..=63 => Some(expr.zero_ext(64 - width)),
        _ => None,
    }
}

fn eval_concrete_u64(expr: &SmtExpr) -> Option<u64> {
    let empty_env = HashMap::new();
    match expr.try_eval(&empty_env).ok()? {
        EvalResult::Bv(value) => Some(value),
        EvalResult::Bv128(value) => u64::try_from(value).ok(),
        // Poison (a trapping-op result) has no defined concrete value; fail closed.
        EvalResult::Bool(_)
        | EvalResult::Float(_)
        | EvalResult::Array { .. }
        | EvalResult::Poison => None,
    }
}

#[cfg(test)]
#[path = "fsym_trust_ir_current_ir_tests.rs"]
mod current_ir_boundary_tests;

#[cfg(test)]
mod tests {
    use super::{
        FSYM_TRUST_IR_MAX_SWITCH_CASES, FSYM_TRUST_IR_POINTER_BITS, FsymTrustIrDiagnosticKind,
        FsymTrustIrSkipReason, FsymTrustIrSolverObligation, FunctionScan, ScanTarget,
        is_pointer_like_ty, parameter_facts, scan_module,
    };

    /// A module pinned to 8-byte pointers.
    const TARGET_64: ScanTarget = ScanTarget {
        pointer_bits: Some(64),
    };
    use crate::fsym_arith::ArithUbKind;
    use trust_ir::inst::{BindingFrameDef, BindingSlot};
    use trust_ir::ty::FatPtrKind;
    use trust_ir::value::BindingFrameId;
    use trust_ir::{
        BinOp, Block, BlockId, Constant, DialectInst, FuncId, FuncTy, FuncTyId, Function, ICmpOp,
        Inst, InstrNode, Module, SwitchCase, Ty, ValueId,
    };

    /// A `FatPtr` parameter must be type-set CONSISTENT: `is_pointer_like_ty`
    /// reports it as a pointer AND `parameter_facts` attaches `PointerFacts`
    /// whose `addr` is the 64-bit DATA-pointer lane — NOT a silent `None`
    /// that would route its derefs to unaccounted/unknown. (Regression guard for
    /// the type-set split between `is_pointer_like_ty` and `bit_width_with`.)
    #[test]
    fn fat_pointer_param_is_pointer_like_and_gets_data_lane_facts() {
        // Sanity: a fat pointer is two pointer-sized lanes (128 on a 64-bit
        // target), which is exactly why the naive width path dropped it.
        assert_eq!(
            Ty::FatPtr(FatPtrKind::Str).bit_width_with(FSYM_TRUST_IR_POINTER_BITS),
            Some(2 * FSYM_TRUST_IR_POINTER_BITS)
        );

        let func = Function::new(
            FuncId::new(0),
            "fatptr_fn",
            FuncTyId::new(0),
            BlockId::new(0),
        );

        for fat in [
            Ty::FatPtr(FatPtrKind::Str),
            Ty::FatPtr(FatPtrKind::Slice(trust_ir::value::TyId::new(0))),
            Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 0 }),
        ] {
            assert!(
                is_pointer_like_ty(&fat),
                "FatPtr must be pointer-like for fact attachment: {fat:?}"
            );
            let facts = parameter_facts(&func, v(0), &fat, Some(FSYM_TRUST_IR_POINTER_BITS));
            let pointer = facts
                .pointer
                .unwrap_or_else(|| panic!("FatPtr param must get PointerFacts, not None: {fat:?}"));
            // The modeled lane is the 64-bit thin data pointer, matching the
            // scanner's `ptr_width: 64` deref obligations.
            assert_eq!(
                pointer.addr.as_ref().unwrap().try_bv_width().unwrap(),
                FSYM_TRUST_IR_POINTER_BITS,
                "FatPtr address must be the 64-bit data lane: {fat:?}"
            );
            assert!(
                facts.expr.is_some(),
                "FatPtr param must get a symbolic expr: {fat:?}"
            );
        }
    }

    fn v(index: u32) -> ValueId {
        ValueId::new(index)
    }

    #[test]
    fn call_boundary_fsym_refuses_valid_no_eh_bodies_before_scanning() {
        for indirect in [false, true] {
            for result in [false, true] {
                for nonexecuted in [false, true] {
                    let mut module = Module::new("fsym_call_boundary");
                    module.target_info = Some(target_info("aarch64-apple-darwin", 8));
                    let returns = if result { vec![Ty::I64] } else { vec![] };
                    let signature = module
                        .add_func_type(FuncTy {
                            params: vec![Ty::I64],
                            returns: returns.clone(),
                            abi: None,
                            is_vararg: false,
                        })
                        .expect("Module::add_func_type: test fixture");
                    let caller_signature = module
                        .add_func_type(FuncTy {
                            params: vec![Ty::Ptr, Ty::I64],
                            returns,
                            abi: None,
                            is_vararg: false,
                        })
                        .expect("Module::add_func_type: test fixture");
                    let mut callee =
                        Function::new(FuncId::new(0), "callee", signature, BlockId::new(0));
                    callee.linkage = trust_ir::Linkage::Internal;
                    let mut callee_block = Block::new(BlockId::new(0));
                    callee_block.params.push((v(0), Ty::I64));
                    callee_block.body.push(InstrNode::new(Inst::Return {
                        values: if result { vec![v(0)] } else { vec![] },
                    }));
                    callee.blocks.push(callee_block);
                    let mut caller =
                        Function::new(FuncId::new(1), "caller", caller_signature, BlockId::new(0));
                    caller.linkage = trust_ir::Linkage::Internal;
                    let mut entry = Block::new(BlockId::new(0));
                    entry.params = vec![(v(0), Ty::Ptr), (v(1), Ty::I64)];
                    let (mut block, pointer, argument, destination) = if nonexecuted {
                        entry.body.push(const_bool(6, false));
                        entry.body.push(InstrNode::new(Inst::CondBr {
                            cond: v(6),
                            then_target: BlockId::new(1),
                            then_args: vec![v(0), v(1)],
                            else_target: BlockId::new(2),
                            else_args: vec![],
                        }));
                        let mut untaken = Block::new(BlockId::new(1));
                        untaken.params = vec![(v(3), Ty::Ptr), (v(4), Ty::I64)];
                        (untaken, v(3), v(4), v(5))
                    } else {
                        (entry.clone(), v(0), v(1), v(2))
                    };
                    let inst = if indirect {
                        Inst::CallIndirectCannotUnwind {
                            callee: pointer,
                            sig: signature,
                            args: vec![argument],
                            calling_conv: trust_ir::CallingConv::C,
                        }
                    } else {
                        Inst::CallCannotUnwind {
                            callee: callee.id,
                            args: vec![argument],
                        }
                    };
                    let expected = crate::fsym_ub_map::fsym_inst_variant_name(&inst);
                    let mut node = InstrNode::new(inst);
                    if result {
                        node.results.push(destination);
                    }
                    block.body.push(node);
                    block.body.push(InstrNode::new(Inst::Return {
                        values: if result { vec![destination] } else { vec![] },
                    }));
                    if nonexecuted {
                        caller.blocks.push(entry);
                    }
                    caller.blocks.push(block);
                    if nonexecuted {
                        let mut exit = Block::new(BlockId::new(2));
                        exit.body.push(InstrNode::new(Inst::Return {
                            values: if result { vec![v(1)] } else { vec![] },
                        }));
                        caller.blocks.push(exit);
                    }
                    module.functions = vec![callee, caller];
                    let errors = trust_ir_build::validate_module(&module);
                    assert!(errors.is_empty(), "fixture must be valid IR: {errors:#?}");
                    assert!(!module.instructions().any(|node| matches!(
                        node.inst,
                        Inst::Invoke { .. } | Inst::LandingPad { .. } | Inst::Resume { .. }
                    )));
                    let report = super::scan_function_in_module(&module, &module.functions[1]);
                    assert_eq!(report.scanned_functions, 0, "{report:?}");
                    assert!(report.diagnostics.is_empty() && report.unknown_obligations.is_empty());
                    assert_eq!(report.skipped_functions.len(), 1, "{report:?}");
                    let skip = &report.skipped_functions[0];
                    assert_eq!(skip.reason, FsymTrustIrSkipReason::UnsupportedInstruction);
                    assert!(
                        skip.detail.contains("non-propagating call boundary")
                            && skip.detail.contains(expected),
                        "{skip:?}"
                    );
                    if nonexecuted {
                        // A genuinely disconnected mutant is not valid IR.
                        // Keep that rejection distinct from the valid untaken
                        // branch above; the standalone fsym body floor must
                        // still refuse its stored boundary without a verdict.
                        let caller = &mut module.functions[1];
                        caller.blocks[0].body = vec![InstrNode::new(Inst::Return {
                            values: if result { vec![v(1)] } else { vec![] },
                        })];
                        caller.blocks.retain(|block| block.id != BlockId::new(2));
                        assert_eq!(
                            trust_ir_build::validate_module(&module),
                            vec![trust_ir_build::ValidationError::UnreachableBlock(1)]
                        );
                        let report = super::scan_function_in_module(&module, &module.functions[1]);
                        assert_eq!(report.scanned_functions, 0);
                        assert_eq!(report.skipped_functions.len(), 1);
                        assert!(report.skipped_functions[0].detail.contains(expected));
                        assert!(
                            report.diagnostics.is_empty() && report.unknown_obligations.is_empty()
                        );
                    }
                }
            }
        }
    }

    /// The `(inst_index, opcode)` projection of the enumerated sites.
    fn site_opcodes(
        sites: Vec<(usize, &'static str, Vec<FsymTrustIrDiagnosticKind>)>,
    ) -> Vec<(usize, &'static str)> {
        sites
            .into_iter()
            .map(|(inst_index, opcode, _)| (inst_index, opcode))
            .collect()
    }

    fn test_module(name: &str, body: Vec<InstrNode>) -> Module {
        test_module_blocks(
            name,
            vec![Block {
                id: BlockId::new(0),
                params: vec![],
                body,
            }],
        )
    }

    fn test_module_blocks(name: &str, blocks: Vec<Block>) -> Module {
        let mut module = Module::new(name);
        module.func_types.push(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "test", FuncTyId::new(0), BlockId::new(0));
        function.blocks = blocks;
        module.functions.push(function);
        module
    }

    fn const_i64(result: u32, value: i64) -> InstrNode {
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(value.into()),
        })
        .with_result(v(result))
    }

    fn const_bool(result: u32, value: bool) -> InstrNode {
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(value),
        })
        .with_result(v(result))
    }

    fn bin_i64(result: u32, op: BinOp, lhs: u32, rhs: u32) -> InstrNode {
        InstrNode::new(Inst::BinOp {
            op,
            ty: Ty::I64,
            lhs: v(lhs),
            rhs: v(rhs),
        })
        .with_result(v(result))
    }

    fn icmp_i64(result: u32, op: ICmpOp, lhs: u32, rhs: u32) -> InstrNode {
        InstrNode::new(Inst::ICmp {
            op,
            ty: Ty::I64,
            lhs: v(lhs),
            rhs: v(rhs),
        })
        .with_result(v(result))
    }

    fn br(target: u32, args: &[u32]) -> InstrNode {
        InstrNode::new(Inst::Br {
            target: BlockId::new(target),
            args: args.iter().copied().map(v).collect(),
        })
    }

    fn condbr(
        cond: u32,
        then_target: u32,
        then_args: &[u32],
        else_target: u32,
        else_args: &[u32],
    ) -> InstrNode {
        InstrNode::new(Inst::CondBr {
            cond: v(cond),
            then_target: BlockId::new(then_target),
            then_args: then_args.iter().copied().map(v).collect(),
            else_target: BlockId::new(else_target),
            else_args: else_args.iter().copied().map(v).collect(),
        })
    }

    fn ret_i64(value: u32) -> InstrNode {
        InstrNode::new(Inst::Return {
            values: vec![v(value)],
        })
    }

    fn assert_skips_unsupported_instruction(module_name: &str, mut body: Vec<InstrNode>) {
        body.push(const_i64(90, 0));
        body.push(ret_i64(90));
        let report = scan_module(&test_module(module_name, body));

        assert_eq!(report.scanned_functions, 0);
        assert_eq!(report.skipped_functions.len(), 1);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::UnsupportedInstruction
        );
        assert!(report.skipped_functions[0].detail.contains("unsupported"));
    }

    fn guarded_null_loop_module(name: &str, trip_count: i64, bad_index: i64) -> Module {
        test_module_blocks(
            name,
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![const_i64(0, 0), br(1, &[0])],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![(v(10), Ty::I64)],
                    body: vec![
                        const_i64(11, trip_count),
                        icmp_i64(12, ICmpOp::Slt, 10, 11),
                        condbr(12, 2, &[], 4, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        const_i64(20, bad_index),
                        icmp_i64(21, ICmpOp::Eq, 10, 20),
                        condbr(21, 3, &[], 5, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(3),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(30)),
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(30),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(31)),
                        br(5, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(4),
                    params: vec![],
                    body: vec![const_i64(40, 0), ret_i64(40)],
                },
                Block {
                    id: BlockId::new(5),
                    params: vec![],
                    body: vec![
                        const_i64(50, 1),
                        bin_i64(51, BinOp::Add, 10, 50),
                        br(1, &[51]),
                    ],
                },
            ],
        )
    }

    #[test]
    fn reports_concrete_null_load() {
        let module = test_module(
            "fsym_null",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].kind,
            FsymTrustIrDiagnosticKind::NullDeref
        );
    }

    #[test]
    fn reports_concrete_division_by_zero() {
        let module = test_module(
            "fsym_divzero",
            vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(42),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::SDiv,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].kind,
            FsymTrustIrDiagnosticKind::Arithmetic
        );
    }

    #[test]
    fn records_symbolic_arithmetic_unknown_solver_candidate() {
        let module = test_module_blocks(
            "fsym_symbolic_sadd",
            vec![Block {
                id: BlockId::new(0),
                params: vec![(v(0), Ty::I8), (v(1), Ty::I8)],
                body: vec![
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Ne,
                        ty: Ty::I8,
                        lhs: v(0),
                        rhs: v(1),
                    })
                    .with_result(v(2)),
                    InstrNode::new(Inst::Assume { cond: v(2) }),
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I8,
                        lhs: v(0),
                        rhs: v(1),
                    })
                    .with_result(v(3)),
                    InstrNode::new(Inst::Return { values: vec![v(3)] }),
                ],
            }],
        );

        let report = scan_module(&module);

        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unknown_obligations.len(), 1);
        assert_eq!(
            report.unknown_obligations[0].kind,
            FsymTrustIrDiagnosticKind::Arithmetic
        );
        let solver_candidate = report.unknown_obligations[0]
            .solver_candidate
            .as_ref()
            .expect("arithmetic unknown should carry a typed solver candidate");
        assert_eq!(solver_candidate.path_guards.len(), 1);
        match &solver_candidate.obligation {
            FsymTrustIrSolverObligation::Arithmetic { kind, width, .. } => {
                assert_eq!(*kind, ArithUbKind::Sadd);
                assert_eq!(*width, 8);
            }
            other => panic!("expected arithmetic solver candidate, got {other:?}"),
        }
    }

    #[test]
    fn reports_concrete_out_of_bounds_load() {
        let module = test_module(
            "fsym_oob",
            vec![
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: None,
                    align: None,
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(0),
                    indices: vec![v(1)],
                    inbounds: false,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(2),
                    volatile: false,
                    align: None,
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].kind,
            FsymTrustIrDiagnosticKind::OutOfBounds
        );
    }

    #[test]
    fn records_symbolic_oob_unknown_solver_candidate() {
        let module = test_module_blocks(
            "fsym_symbolic_oob",
            vec![Block {
                id: BlockId::new(0),
                params: vec![(v(0), Ty::I64)],
                body: vec![
                    InstrNode::new(Inst::Alloca {
                        ty: Ty::I64,
                        count: None,
                        align: None,
                    })
                    .with_result(v(1)),
                    init_slot(1, 9)[0].clone(),
                    init_slot(1, 9)[1].clone(),
                    InstrNode::new(Inst::GEP {
                        pointee_ty: Ty::I64,
                        base: v(1),
                        indices: vec![v(0)],
                        inbounds: false,
                    })
                    .with_result(v(2)),
                    InstrNode::new(Inst::Load {
                        ty: Ty::I64,
                        ptr: v(2),
                        volatile: false,
                        align: None,
                    })
                    .with_result(v(3)),
                    InstrNode::new(Inst::Return { values: vec![v(3)] }),
                ],
            }],
        );

        let report = scan_module(&module);

        assert!(report.diagnostics.is_empty());
        // The symbolic index owes a GEP-arithmetic obligation (negative or
        // overflowing index) and the load a bounds one; both escalate. The
        // load is aligned (`i * 8` has three trailing zeros) and reads a
        // fully initialized slot.
        assert_eq!(
            unknown_kinds(&report),
            vec![
                FsymTrustIrDiagnosticKind::PointerArithmetic,
                FsymTrustIrDiagnosticKind::OutOfBounds
            ],
            "{:?}",
            report.unknown_obligations
        );
        let gep = &report.unknown_obligations[0];
        assert!(matches!(
            gep.solver_candidate
                .as_ref()
                .map(|candidate| &candidate.obligation),
            Some(FsymTrustIrSolverObligation::Arithmetic {
                kind: ArithUbKind::GepOffset {
                    elem_size: 8,
                    signed_index: true,
                    limit: u64::MAX,
                },
                width: 64,
                ..
            })
        ));
        let unknown = &report.unknown_obligations[1];
        assert_eq!(unknown.kind, FsymTrustIrDiagnosticKind::OutOfBounds);
        assert!(
            unknown
                .candidate_expression
                .as_deref()
                .is_some_and(|candidate| candidate.contains("bounds side condition"))
        );
        let solver_candidate = unknown
            .solver_candidate
            .as_ref()
            .expect("symbolic OOB unknown should carry a typed solver candidate");
        assert!(solver_candidate.path_guards.is_empty());
        match &solver_candidate.obligation {
            FsymTrustIrSolverObligation::OutOfBounds {
                access_size_bytes,
                width,
                ..
            } => {
                assert_eq!(*access_size_bytes, 8);
                assert_eq!(*width, 64);
            }
            other => panic!("expected OOB solver candidate, got {other:?}"),
        }
    }

    #[test]
    fn reports_concrete_use_after_free() {
        let module = test_module(
            "fsym_uaf",
            vec![
                // A heap object: freeing it is legal, reading it after is not.
                heap_i64(0),
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].kind,
            FsymTrustIrDiagnosticKind::UseAfterFree
        );
    }

    #[test]
    fn skips_undef_instead_of_silently_scanning() {
        assert_skips_unsupported_instruction(
            "fsym_undef_skip",
            vec![InstrNode::new(Inst::Undef { ty: Ty::I64 }).with_result(v(0))],
        );
    }

    #[test]
    fn skips_call_indirect_instead_of_silently_scanning() {
        assert_skips_unsupported_instruction(
            "fsym_call_indirect_skip",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                InstrNode::new(Inst::CallIndirect {
                    callee: v(0),
                    sig: FuncTyId::new(0),
                    args: vec![],
                    calling_conv: trust_ir::CallingConv::C,
                })
                .with_result(v(1)),
            ],
        );
    }

    #[test]
    fn skips_dialect_op_instead_of_silently_scanning() {
        assert_skips_unsupported_instruction(
            "fsym_dialect_skip",
            vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    DialectInst::new("verif", "opaque").with_result_ty(Ty::I64),
                )))
                .with_result(v(0)),
            ],
        );
    }

    #[test]
    fn skips_binding_frame_ops_instead_of_silently_scanning() {
        let def = BindingFrameDef::new(
            BindingFrameId::new(0),
            "q",
            vec![BindingSlot::new("i", Ty::I64)],
        );

        assert_skips_unsupported_instruction(
            "fsym_binding_frame_skip",
            vec![
                InstrNode::new(Inst::OpenFrame { def }).with_result(v(0)),
                const_i64(1, 7),
                InstrNode::new(Inst::BindSlot {
                    frame: v(0),
                    slot: 0,
                    value: v(1),
                })
                .with_result(v(2)),
            ],
        );
    }

    #[test]
    fn skips_arc_ops_instead_of_silently_scanning() {
        assert_skips_unsupported_instruction(
            "fsym_arc_skip",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                InstrNode::new(Inst::IsUnique { ptr: v(0) }).with_result(v(1)),
            ],
        );
    }

    #[test]
    fn follows_condbr_taken_path_with_block_arg() {
        let module = test_module_blocks(
            "fsym_condbr_taken",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::Bool,
                            value: Constant::Bool(true),
                        })
                        .with_result(v(0)),
                        InstrNode::new(Inst::NullPtr).with_result(v(1)),
                        InstrNode::new(Inst::CondBr {
                            cond: v(0),
                            then_target: BlockId::new(1),
                            then_args: vec![v(1)],
                            else_target: BlockId::new(2),
                            else_args: vec![],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![(v(10), Ty::Ptr)],
                    body: vec![
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(10),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(11)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(11)],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(20)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(20)],
                        }),
                    ],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].kind,
            FsymTrustIrDiagnosticKind::NullDeref
        );
        assert_eq!(report.diagnostics[0].block, 1);
    }

    #[test]
    fn suppresses_ub_on_infeasible_condbr_arm() {
        let module = test_module_blocks(
            "fsym_condbr_infeasible",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(7),
                        })
                        .with_result(v(0)),
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(7),
                        })
                        .with_result(v(1)),
                        InstrNode::new(Inst::ICmp {
                            op: ICmpOp::Eq,
                            ty: Ty::I64,
                            lhs: v(0),
                            rhs: v(1),
                        })
                        .with_result(v(2)),
                        InstrNode::new(Inst::CondBr {
                            cond: v(2),
                            then_target: BlockId::new(1),
                            then_args: vec![],
                            else_target: BlockId::new(2),
                            else_args: vec![],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(10)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(10)],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(20)),
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(20),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(21)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(21)],
                        }),
                    ],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert!(report.diagnostics.is_empty());
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn scans_concrete_ub_in_static_bounded_loop() {
        let module = guarded_null_loop_module("fsym_loop_concrete_ub", 4, 2);

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].kind,
            FsymTrustIrDiagnosticKind::NullDeref
        );
        assert_eq!(report.diagnostics[0].block, 3);
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn suppresses_ub_on_infeasible_loop_iteration() {
        let module = guarded_null_loop_module("fsym_loop_infeasible_iteration", 2, 3);

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert!(report.diagnostics.is_empty());
        assert!(report.unknown_obligations.is_empty());
    }

    /// Fixture: a 2-iteration symbolic loop whose block 2 dereferences an
    /// unconstrained pointer FUNCTION PARAM `v(0): Ptr` with no not-null
    /// annotation on any path. That `Load` is a genuine potential null deref;
    /// each loop iteration is a distinct reachable deref site. Kept as the
    /// regression fixture for the trust-ir `bit_width()`-on-pointers fail-open.
    fn symbolic_loop_ptr_module(ptr_ty: Ty) -> Module {
        test_module_blocks(
            "fsym_loop_symbolic_ptr",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![(v(0), ptr_ty)],
                    body: vec![const_i64(1, 0), br(1, &[1])],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![(v(10), Ty::I64)],
                    body: vec![
                        const_i64(11, 2),
                        icmp_i64(12, ICmpOp::Slt, 10, 11),
                        condbr(12, 2, &[], 4, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(0),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(20)),
                        br(3, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(3),
                    params: vec![],
                    body: vec![
                        const_i64(30, 1),
                        bin_i64(31, BinOp::Add, 10, 30),
                        br(1, &[31]),
                    ],
                },
                Block {
                    id: BlockId::new(4),
                    params: vec![],
                    body: vec![const_i64(40, 0), ret_i64(40)],
                },
            ],
        )
    }

    /// Principled property (replaces the old `assert_eq!(len, 2)` magic
    /// number): the unconstrained-pointer deref MUST be ACCOUNTED FOR as an
    /// unknown null-deref carrying a typed solver candidate — never silently
    /// dropped — and the fail-closed deref-coverage invariant must report no
    /// gap. We do not hinge on the exact obligation count; we assert the
    /// obligations are the right KIND, are tied to the reachable deref site,
    /// and that every reachable deref is covered.
    #[test]
    fn symbolic_loop_ptr_deref_is_accounted_as_unknown_null() {
        let module = symbolic_loop_ptr_module(Ty::Ptr);

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        // The deref is a candidate, not a proven UB or a proven-safe pass.
        assert!(report.diagnostics.is_empty());
        // FAIL-CLOSED invariant: no reachable deref was dropped.
        assert!(
            report.coverage_errors.is_empty(),
            "deref-coverage gap on a fixture that should be fully accounted: {:?}",
            report.coverage_errors
        );

        // The unconstrained-ptr deref IS accounted for as an unknown
        // null-deref with a typed solver candidate. The Load at bb2 is the
        // only deref site, so every unknown obligation is rooted there: the
        // null-deref, and the obligations a parameter pointer cannot
        // discharge (its object's extent, lifetime, alignment and contents
        // belong to the caller and are not tracked).
        assert!(
            !report.unknown_obligations.is_empty(),
            "the unconstrained-pointer deref must be recorded, not dropped"
        );
        assert!(
            report
                .unknown_obligations
                .iter()
                .all(|unknown| unknown.block == 2 && unknown.inst_index == 0),
            "every recorded obligation must be rooted at the bb2 Load: {:?}",
            report.unknown_obligations
        );
        let kinds = unknown_kinds(&report);
        let per_load = [
            FsymTrustIrDiagnosticKind::NullDeref,
            FsymTrustIrDiagnosticKind::OutOfBounds,
            FsymTrustIrDiagnosticKind::UseAfterFree,
            FsymTrustIrDiagnosticKind::Misaligned,
            FsymTrustIrDiagnosticKind::Uninitialized,
        ];
        assert_eq!(kinds.len() % per_load.len(), 0, "{kinds:?}");
        assert!(
            kinds.chunks(per_load.len()).all(|chunk| chunk == per_load),
            "{kinds:?}"
        );

        // The deepest-path null obligation carries the loop guards and a
        // typed NullDeref solver candidate the caller can escalate.
        let unknown = report
            .unknown_obligations
            .iter()
            .filter(|unknown| unknown.kind == FsymTrustIrDiagnosticKind::NullDeref)
            .max_by_key(|unknown| unknown.path_guards.len())
            .expect("bounded loop should produce a symbolic null obligation");
        assert!(unknown.path_guards.len() >= 2);
        let solver_candidate = unknown
            .solver_candidate
            .as_ref()
            .expect("loop null unknown should carry a typed solver candidate");
        assert_eq!(
            solver_candidate.path_guards.len(),
            unknown.path_guards.len()
        );
        assert!(matches!(
            solver_candidate.obligation,
            FsymTrustIrSolverObligation::NullDeref { .. }
        ));
    }

    /// Regression case for the original fail-open: the bumped trust-ir made
    /// `Ty::bit_width()` return `None` for pointer types, so a `Ptr` param lost
    /// its facts and its deref produced ZERO obligations (a silent pass). The
    /// scanner must now record one obligation per reachable loop iteration —
    /// and the non-bare pointer variants must NOT be silently dropped either.
    #[test]
    fn symbolic_loop_ptr_deref_records_per_iteration_obligations() {
        for ptr_ty in [
            Ty::Ptr,
            Ty::PtrConst(Box::new(Ty::I64)),
            Ty::PtrMut(Box::new(Ty::I64)),
            Ty::Ref(Box::new(Ty::I64)),
            Ty::RefMut(Box::new(Ty::I64)),
        ] {
            let module = symbolic_loop_ptr_module(ptr_ty.clone());
            let report = scan_module(&module);
            assert!(
                report.coverage_errors.is_empty(),
                "{ptr_ty:?}: unexpected coverage gap"
            );
            // Two reachable iterations of the bb2 Load => two null obligations,
            // proving the regression (0 obligations) is fixed for every
            // pointer-like parameter type. Each iteration also owes the four
            // obligations a parameter's untracked object cannot discharge.
            let null = report
                .unknown_obligations
                .iter()
                .filter(|unknown| unknown.kind == FsymTrustIrDiagnosticKind::NullDeref)
                .count();
            assert_eq!(
                null, 2,
                "{ptr_ty:?}: expected one null obligation per loop iteration"
            );
            assert_eq!(
                report.unknown_obligations.len(),
                2 * 5,
                "{ptr_ty:?}: null, bounds, lifetime, alignment, initialization per iteration"
            );
            assert!(report.diagnostics.is_empty(), "{ptr_ty:?}");
        }
    }

    /// The fail-closed deref-coverage invariant must FIRE when a reachable
    /// deref's verdict is artificially dropped. This tests the GUARD itself:
    /// we inject the historical fail-open behaviour (silent early return in
    /// `check_null`) and assert `run_block` raises an `FsymCoverageError`
    /// rather than letting the obligation vanish. Without the invariant this
    /// is exactly the regression that slipped through.
    #[test]
    fn deref_coverage_invariant_fails_closed_on_dropped_verdict() {
        let module = symbolic_loop_ptr_module(Ty::Ptr);
        let function = &module.functions[0];
        // Block 2 holds the reachable Load deref site.
        let block = function
            .blocks
            .iter()
            .find(|block| block.id == BlockId::new(2))
            .expect("fixture has block 2");

        // Sanity: with the verdict recorded normally, the site is covered and
        // no coverage error is raised.
        let mut ok_scan = FunctionScan::new(&module, function, block, TARGET_64);
        ok_scan.run_block();
        assert!(
            ok_scan.coverage_errors.is_empty(),
            "a recorded deref must not trip the coverage invariant"
        );

        // Inject the dropped-verdict fault: `check_null` returns without
        // recording, so the reachable Load records NO verdict.
        let mut dropped_scan = FunctionScan::new(&module, function, block, TARGET_64);
        dropped_scan.force_drop_deref = true;
        dropped_scan.run_block();

        assert_eq!(
            dropped_scan.coverage_errors.len(),
            1,
            "a dropped reachable deref must raise exactly one coverage error"
        );
        let error = &dropped_scan.coverage_errors[0];
        assert_eq!(error.block, 2);
        assert_eq!(error.inst_index, 0);
        assert_eq!(error.opcode, "Load");
        assert!(error.function.contains("test"));
    }

    #[test]
    fn skips_loop_without_static_trip_count() {
        let module = test_module_blocks(
            "fsym_loop_symbolic_trip_skip",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![(v(0), Ty::I64)],
                    body: vec![const_i64(1, 0), br(1, &[1])],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![(v(10), Ty::I64)],
                    body: vec![icmp_i64(11, ICmpOp::Slt, 10, 0), condbr(11, 2, &[], 3, &[])],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        const_i64(20, 1),
                        bin_i64(21, BinOp::Add, 10, 20),
                        br(1, &[21]),
                    ],
                },
                Block {
                    id: BlockId::new(3),
                    params: vec![],
                    body: vec![const_i64(30, 0), ret_i64(30)],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(report.skipped_functions.len(), 1);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::Loop
        );
        assert!(
            report.skipped_functions[0]
                .detail
                .contains("trip count is not statically bounded")
        );
    }

    #[test]
    fn skips_unsupported_loop_carried_pointer_state() {
        let module = test_module_blocks(
            "fsym_loop_pointer_state_skip",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::NullPtr).with_result(v(0)), br(1, &[0])],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![(v(10), Ty::Ptr)],
                    body: vec![const_bool(11, true), condbr(11, 1, &[10], 2, &[])],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![const_i64(20, 0), ret_i64(20)],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(report.skipped_functions.len(), 1);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::Loop
        );
        assert!(
            report.skipped_functions[0]
                .detail
                .contains("unsupported state type")
        );
    }

    #[test]
    fn skips_cyclic_cfgs_instead_of_unrolling_loops() {
        let module = test_module_blocks(
            "fsym_loop_skip",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Br {
                        target: BlockId::new(1),
                        args: vec![],
                    })],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Br {
                        target: BlockId::new(1),
                        args: vec![],
                    })],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(report.skipped_functions.len(), 1);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::Loop
        );
        assert!(
            report.skipped_functions[0]
                .detail
                .contains("conditional static-bound check")
        );
    }

    #[test]
    fn skips_switch_cycles_instead_of_unrolling() {
        let module = test_module_blocks(
            "fsym_switch_cycle_skip",
            vec![Block {
                id: BlockId::new(0),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    })
                    .with_result(v(0)),
                    InstrNode::new(Inst::Switch {
                        value: v(0),
                        default: BlockId::new(0),
                        default_args: vec![],
                        cases: vec![SwitchCase {
                            value: Constant::Int(1),
                            target: BlockId::new(0),
                            args: vec![],
                        }],
                        exhaustive_enum_unreachable: false,
                    }),
                ],
            }],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(report.skipped_functions.len(), 1);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::Loop
        );
    }

    #[test]
    fn scans_concrete_switch_to_selected_ub_arm() {
        let module = test_module_blocks(
            "fsym_switch_concrete_ub",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(1),
                        })
                        .with_result(v(0)),
                        InstrNode::new(Inst::Switch {
                            value: v(0),
                            default: BlockId::new(3),
                            default_args: vec![],
                            cases: vec![
                                SwitchCase {
                                    value: Constant::Int(0),
                                    target: BlockId::new(1),
                                    args: vec![],
                                },
                                SwitchCase {
                                    value: Constant::Int(1),
                                    target: BlockId::new(2),
                                    args: vec![],
                                },
                            ],
                            exhaustive_enum_unreachable: false,
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(10)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(10)],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(20)),
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(20),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(21)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(21)],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(3),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(9),
                        })
                        .with_result(v(30)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(30)],
                        }),
                    ],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].kind,
            FsymTrustIrDiagnosticKind::NullDeref
        );
        assert_eq!(report.diagnostics[0].block, 2);
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn suppresses_ub_on_infeasible_switch_arm() {
        let module = test_module_blocks(
            "fsym_switch_infeasible",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(0)),
                        InstrNode::new(Inst::Switch {
                            value: v(0),
                            default: BlockId::new(2),
                            default_args: vec![],
                            cases: vec![SwitchCase {
                                value: Constant::Int(1),
                                target: BlockId::new(1),
                                args: vec![],
                            }],
                            exhaustive_enum_unreachable: false,
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(10)),
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(10),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(11)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(11)],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(7),
                        })
                        .with_result(v(20)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(20)],
                        }),
                    ],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert!(report.diagnostics.is_empty());
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn records_symbolic_switch_unknown_solver_candidate() {
        let module = test_module_blocks(
            "fsym_switch_symbolic",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![(v(0), Ty::I8)],
                    body: vec![InstrNode::new(Inst::Switch {
                        value: v(0),
                        default: BlockId::new(2),
                        default_args: vec![],
                        cases: vec![SwitchCase {
                            value: Constant::Int(1),
                            target: BlockId::new(1),
                            args: vec![],
                        }],
                        exhaustive_enum_unreachable: false,
                    })],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(10)),
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(10),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(11)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(11)],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(20)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(20)],
                        }),
                    ],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unknown_obligations.len(), 1);
        assert_eq!(
            report.unknown_obligations[0].kind,
            FsymTrustIrDiagnosticKind::NullDeref
        );
        assert_eq!(report.unknown_obligations[0].path_guards.len(), 1);
        let solver_candidate = report.unknown_obligations[0]
            .solver_candidate
            .as_ref()
            .expect("switch null unknown should carry a typed solver candidate");
        assert_eq!(solver_candidate.path_guards.len(), 1);
        assert!(matches!(
            solver_candidate.obligation,
            FsymTrustIrSolverObligation::NullDeref { .. }
        ));
    }

    #[test]
    fn skips_large_switches() {
        let cases = (0..=FSYM_TRUST_IR_MAX_SWITCH_CASES)
            .map(|index| SwitchCase {
                value: Constant::Int(index as i128),
                target: BlockId::new(1),
                args: vec![],
            })
            .collect();
        let module = test_module_blocks(
            "fsym_large_switch_skip",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(0)),
                        InstrNode::new(Inst::Switch {
                            value: v(0),
                            default: BlockId::new(1),
                            default_args: vec![],
                            cases,
                            exhaustive_enum_unreachable: false,
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(1)),
                        InstrNode::new(Inst::Return { values: vec![v(1)] }),
                    ],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(report.skipped_functions.len(), 1);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::Switch
        );
        assert!(
            report.skipped_functions[0]
                .detail
                .contains("over fsym bound")
        );
    }

    #[test]
    fn reports_typed_unsupported_switch_skip() {
        let module = test_module_blocks(
            "fsym_switch_unsupported_skip",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::Bool,
                            value: Constant::Bool(true),
                        })
                        .with_result(v(0)),
                        InstrNode::new(Inst::Switch {
                            value: v(0),
                            default: BlockId::new(1),
                            default_args: vec![],
                            cases: vec![SwitchCase {
                                value: Constant::Bool(true),
                                target: BlockId::new(1),
                                args: vec![],
                            }],
                            exhaustive_enum_unreachable: false,
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(1)),
                        InstrNode::new(Inst::Return { values: vec![v(1)] }),
                    ],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(report.skipped_functions.len(), 1);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::Switch
        );
        assert!(
            report.skipped_functions[0]
                .detail
                .contains("outside bounded fsym support")
        );
    }
    // -- Bulk memory (trust-ir WS3.20 `MemCopy` / `MemSet`) -----------------
    //
    // Both are memory accesses of `bytes` bytes at `dst` (and, for `MemCopy`,
    // at `src`), so they owe the same null / bounds / use-after-free verdicts
    // a `Store` / `Load` owes. The first three fixtures are the adversarial
    // verifier's measured cases against trust-cg 31f0fa52, where each scanned
    // clean (diagnostics=[], unknowns=0, coverage_errors=0).

    fn const_u64(result: u32, value: u64) -> InstrNode {
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(value.into()),
        })
        .with_result(v(result))
    }

    fn const_u8(result: u32, value: u8) -> InstrNode {
        InstrNode::new(Inst::Const {
            ty: Ty::U8,
            value: Constant::Int(value.into()),
        })
        .with_result(v(result))
    }

    fn alloca_i64(result: u32) -> InstrNode {
        InstrNode::new(Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: None,
        })
        .with_result(v(result))
    }

    /// A heap `i64`: the allocation a `Dealloc` may legally free.
    fn heap_i64(result: u32) -> InstrNode {
        InstrNode::new(Inst::HeapAlloc {
            ty: Ty::I64,
            count: None,
            align: None,
            origin: trust_ir::inst::AllocOrigin::CMalloc,
        })
        .with_result(v(result))
    }

    /// `store u64 7 -> ptr`, so a later load from `ptr` reads written bytes
    /// (its value stays unmodeled: loaded values always are).
    fn init_slot(ptr: u32, scratch: u32) -> [InstrNode; 2] {
        [
            const_u64(scratch, 7),
            InstrNode::new(Inst::Store {
                ty: Ty::U64,
                ptr: v(ptr),
                value: v(scratch),
                volatile: false,
                align: None,
            }),
        ]
    }

    fn memset(dst: u32, byte: u32, bytes: u32) -> InstrNode {
        InstrNode::new(Inst::MemSet {
            dst: v(dst),
            byte: v(byte),
            bytes: v(bytes),
        })
    }

    fn memcopy(dst: u32, src: u32, bytes: u32, overlap: bool) -> InstrNode {
        InstrNode::new(Inst::MemCopy {
            dst: v(dst),
            src: v(src),
            bytes: v(bytes),
            overlap,
        })
    }

    fn scan_body(name: &str, mut body: Vec<InstrNode>) -> super::FsymTrustIrReport {
        body.push(const_i64(99, 0));
        body.push(ret_i64(99));
        scan_module(&test_module(name, body))
    }

    fn diagnostic_kinds(report: &super::FsymTrustIrReport) -> Vec<FsymTrustIrDiagnosticKind> {
        report
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.kind)
            .collect()
    }

    #[test]
    fn memset_through_null_reports_null_deref() {
        let report = scan_body(
            "fsym_memset_null",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                const_u64(1, 8),
                const_u8(2, 0),
                memset(0, 2, 1),
            ],
        );

        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert!(report.coverage_errors.is_empty());
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::NullDeref]
        );
        assert_eq!(report.diagnostics[0].inst_index, 3);
    }

    #[test]
    fn memcopy_null_to_null_reports_null_deref() {
        let report = scan_body(
            "fsym_memcopy_null",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                const_u64(1, 8),
                memcopy(0, 0, 1, false),
            ],
        );

        assert_eq!(report.scanned_functions, 1);
        assert!(report.coverage_errors.is_empty());
        // One verdict per operand: the destination and the source are both
        // the null pointer.
        assert_eq!(
            diagnostic_kinds(&report),
            vec![
                FsymTrustIrDiagnosticKind::NullDeref,
                FsymTrustIrDiagnosticKind::NullDeref
            ]
        );
        assert!(report.diagnostics.iter().all(|d| d.inst_index == 2));
    }

    #[test]
    fn oversized_memset_into_alloca_reports_out_of_bounds() {
        let report = scan_body(
            "fsym_memset_oob",
            vec![
                alloca_i64(0),
                const_u64(1, 64),
                const_u8(2, 0),
                memset(0, 2, 1),
            ],
        );

        assert_eq!(report.scanned_functions, 1);
        assert!(report.coverage_errors.is_empty());
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
        assert!(report.diagnostics[0].message.contains("64-byte"));
    }

    #[test]
    fn in_bounds_memset_and_memcopy_on_allocas_pass() {
        let report = scan_body(
            "fsym_bulk_in_bounds",
            vec![
                alloca_i64(0),
                alloca_i64(1),
                const_u64(2, 8),
                const_u8(3, 0xab),
                memset(0, 3, 2),
                memcopy(1, 0, 2, false),
                memcopy(1, 0, 2, true),
            ],
        );

        assert_eq!(report.scanned_functions, 1);
        assert!(report.coverage_errors.is_empty());
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
        assert!(
            report.unknown_obligations.is_empty(),
            "{:?}",
            report.unknown_obligations
        );
    }
    /// `[I64; 4]` (32 bytes) at `result`, with its element count at `count`.
    fn alloca_i64_array4(count: u32, result: u32) -> Vec<InstrNode> {
        vec![
            const_i64(count, 4),
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: Some(v(count)),
                align: None,
            })
            .with_result(v(result)),
        ]
    }

    fn byte_gep(result: u32, base: u32, index: u32) -> InstrNode {
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::U8,
            base: v(base),
            indices: vec![v(index)],
            inbounds: false,
        })
        .with_result(v(result))
    }

    fn scan_with_params(
        name: &str,
        params: Vec<(ValueId, Ty)>,
        mut body: Vec<InstrNode>,
    ) -> super::FsymTrustIrReport {
        body.push(const_i64(99, 0));
        body.push(ret_i64(99));
        scan_module(&test_module_blocks(
            name,
            vec![Block {
                id: BlockId::new(0),
                params,
                body,
            }],
        ))
    }

    #[test]
    fn usize_count_memset_into_alloca_reports_out_of_bounds() {
        // A target-pinned module types the count `Usize`; a constant one must
        // be concrete, not an unmodeled value.
        let body = |ret: u32| {
            vec![
                alloca_i64(0),
                InstrNode::new(Inst::Const {
                    ty: Ty::Usize,
                    value: Constant::Int(9),
                })
                .with_result(v(1)),
                const_u8(2, 0),
                memset(0, 2, 1),
                const_i64(ret, 0),
                ret_i64(ret),
            ]
        };
        let mut module = test_module("fsym_memset_usize_oob", body(99));
        module.target_info = Some(target_info("aarch64-apple-darwin", 8));
        let report = scan_module(&module);

        assert!(report.coverage_errors.is_empty());
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
        assert!(report.unknown_obligations.is_empty());

        // The same function in a target-free module: `Usize` has no pinned
        // width, so it is refused by name rather than modeled at a guess.
        let report = scan_module(&test_module("fsym_memset_usize_target_free", body(99)));
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::PointerWidth
        );
        assert!(
            report.skipped_functions[0]
                .detail
                .contains("no target_info"),
            "{}",
            report.skipped_functions[0].detail
        );
    }

    #[test]
    fn oversized_memcopy_source_reports_out_of_bounds() {
        let mut body = alloca_i64_array4(0, 1);
        body.extend([alloca_i64(2), const_u64(3, 16), memcopy(1, 2, 3, false)]);
        let report = scan_body("fsym_memcopy_src_oob", body);

        assert!(report.coverage_errors.is_empty());
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
        assert!(report.diagnostics[0].message.contains("MemCopy source"));
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn zero_byte_bulk_ops_through_null_are_defined_no_ops() {
        let report = scan_body(
            "fsym_bulk_zero",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                const_u64(1, 0),
                const_u8(2, 0),
                memset(0, 2, 1),
                memcopy(0, 0, 1, false),
            ],
        );

        assert_eq!(report.scanned_functions, 1);
        assert!(report.coverage_errors.is_empty());
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn symbolic_count_memset_is_unknown_never_pass() {
        // Into a real 8-byte object: the count is a parameter, so the range
        // cannot be bounded — its start is (offset 0), its length and end
        // are Unknowns escalated with the `bytes != 0` guard.
        let report = scan_with_params(
            "fsym_memset_symbolic_alloca",
            vec![(v(10), Ty::U64)],
            vec![alloca_i64(0), const_u8(1, 0), memset(0, 1, 10)],
        );
        assert!(report.coverage_errors.is_empty());
        assert!(report.diagnostics.is_empty());
        let kinds: Vec<_> = report
            .unknown_obligations
            .iter()
            .map(|unknown| unknown.kind)
            .collect();
        assert_eq!(
            kinds,
            vec![
                FsymTrustIrDiagnosticKind::OutOfBounds,
                FsymTrustIrDiagnosticKind::OutOfBounds
            ]
        );
        for (unknown, what) in report.unknown_obligations.iter().zip(["length", "end"]) {
            assert!(unknown.label.contains(what), "{}", unknown.label);
            let candidate = unknown
                .solver_candidate
                .as_ref()
                .expect("a modeled count keeps a typed solver candidate");
            assert_eq!(candidate.path_guards.len(), 1, "{candidate:?}");
        }

        // Through null: UB only when the count is nonzero, so the evaluator
        // must not claim a concrete witness, and the solver candidate must
        // carry the `bytes != 0` guard.
        let report = scan_with_params(
            "fsym_memset_symbolic_null",
            vec![(v(10), Ty::U64)],
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                const_u8(1, 0),
                memset(0, 1, 10),
            ],
        );
        assert!(report.coverage_errors.is_empty());
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
        let null = report
            .unknown_obligations
            .iter()
            .find(|unknown| unknown.kind == FsymTrustIrDiagnosticKind::NullDeref)
            .expect("null obligation recorded as unknown");
        let candidate = null
            .solver_candidate
            .as_ref()
            .expect("symbolic count keeps a typed solver candidate");
        assert_eq!(candidate.path_guards.len(), 1);
        assert!(
            candidate.path_guards[0].to_string().contains("test_arg10"),
            "{}",
            candidate.path_guards[0]
        );
        assert!(
            report
                .unknown_obligations
                .iter()
                .any(|unknown| unknown.kind == FsymTrustIrDiagnosticKind::OutOfBounds)
        );
    }

    #[test]
    fn unmodeled_count_memset_through_null_is_unknown_without_solver_candidate() {
        // The count is loaded from memory: no modeled value, so neither a
        // concrete verdict nor a solver candidate over an invented input.
        let report = scan_body(
            "fsym_memset_unmodeled_null",
            vec![
                alloca_i64(0),
                const_u64(1, 8),
                InstrNode::new(Inst::Store {
                    ty: Ty::U64,
                    ptr: v(0),
                    value: v(1),
                    volatile: false,
                    align: None,
                }),
                InstrNode::new(Inst::Load {
                    ty: Ty::U64,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::NullPtr).with_result(v(3)),
                const_u8(4, 0),
                memset(3, 4, 2),
            ],
        );

        assert!(report.coverage_errors.is_empty());
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
        let bulk: Vec<_> = report
            .unknown_obligations
            .iter()
            .filter(|unknown| unknown.inst_index == 6)
            .collect();
        assert!(
            bulk.iter()
                .any(|unknown| unknown.kind == FsymTrustIrDiagnosticKind::NullDeref)
        );
        assert!(
            bulk.iter()
                .any(|unknown| unknown.kind == FsymTrustIrDiagnosticKind::OutOfBounds)
        );
        assert!(
            bulk.iter()
                .all(|unknown| unknown.solver_candidate.is_none())
        );
    }

    #[test]
    fn memset_after_free_reports_use_after_free() {
        let report = scan_body(
            "fsym_memset_uaf",
            vec![
                heap_i64(0),
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
                const_u64(1, 8),
                const_u8(2, 0),
                memset(0, 2, 1),
            ],
        );

        assert!(report.coverage_errors.is_empty());
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::UseAfterFree]
        );
        assert_eq!(report.diagnostics[0].inst_index, 4);
    }

    #[test]
    fn symbolic_count_access_after_free_is_unknown_and_not_replayed_later() {
        // `memset(p, 0, n)` after `free(p)` is UB only for `n != 0`: an
        // Unknown there, and it must not resurface as a definite use at the
        // later, unrelated load.
        let report = scan_with_params(
            "fsym_memset_symbolic_uaf",
            vec![(v(10), Ty::U64)],
            vec![
                heap_i64(0),
                alloca_i64(1),
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
                const_u8(2, 0),
                memset(0, 2, 10),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(1),
                    volatile: false,
                    align: None,
                })
                .with_result(v(3)),
            ],
        );

        assert!(report.coverage_errors.is_empty());
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
        assert!(report.unknown_obligations.iter().any(|unknown| {
            unknown.kind == FsymTrustIrDiagnosticKind::UseAfterFree && unknown.inst_index == 4
        }));
    }

    #[test]
    fn overlapping_memcpy_within_one_object_reports_overlap() {
        let mut body = alloca_i64_array4(0, 1);
        body.extend([
            const_i64(2, 8),
            byte_gep(3, 1, 2),
            const_u64(4, 16),
            // dst [8, 24) and src [0, 16) of the same 32-byte object.
            memcopy(3, 1, 4, false),
        ]);
        let report = scan_body("fsym_memcpy_overlap", body.clone());
        assert!(report.coverage_errors.is_empty());
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::Overlap]
        );
        assert!(report.unknown_obligations.is_empty());

        // `memmove` semantics define the overlapping copy.
        let last = body.len() - 1;
        body[last] = memcopy(3, 1, 4, true);
        let report = scan_body("fsym_memmove_overlap", body);
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn disjoint_memcpy_within_one_object_passes() {
        let mut body = alloca_i64_array4(0, 1);
        body.extend([
            const_i64(2, 16),
            byte_gep(3, 1, 2),
            const_u64(4, 16),
            // dst [16, 32) and src [0, 16): adjacent, not overlapping.
            memcopy(3, 1, 4, false),
        ]);
        let report = scan_body("fsym_memcpy_disjoint", body);
        assert!(report.coverage_errors.is_empty());
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn undecidable_memcpy_overlap_is_unknown() {
        // Two pointer parameters: nothing relates their addresses.
        let report = scan_with_params(
            "fsym_memcpy_overlap_unknown",
            vec![(v(10), Ty::Ptr), (v(11), Ty::Ptr)],
            vec![const_u64(0, 8), memcopy(10, 11, 0, false)],
        );
        assert!(report.coverage_errors.is_empty());
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
        assert!(
            report
                .unknown_obligations
                .iter()
                .any(|unknown| unknown.kind == FsymTrustIrDiagnosticKind::Overlap)
        );
    }

    #[test]
    fn bulk_memory_ops_are_deref_coverage_sites() {
        let module = test_module(
            "fsym_bulk_coverage",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                const_u64(1, 8),
                const_u8(2, 0),
                memset(0, 2, 1),
                memcopy(0, 0, 1, false),
                const_i64(3, 0),
                ret_i64(3),
            ],
        );
        let function = &module.functions[0];
        let block = &function.blocks[0];
        assert_eq!(
            site_opcodes(super::reachable_obligation_sites(&module, block)),
            vec![(3, "MemSet"), (4, "MemCopy")]
        );

        // Dropping the bulk verdicts must trip the fail-closed invariant.
        let mut dropped = FunctionScan::new(&module, function, block, TARGET_64);
        dropped.force_drop_deref = true;
        dropped.run_block();
        // One coverage error per dropped obligation class; one row per site.
        let mut opcodes: Vec<_> = dropped
            .coverage_errors
            .iter()
            .map(|error| (error.inst_index, error.opcode))
            .collect();
        opcodes.dedup();
        assert_eq!(opcodes, vec![(3, "MemSet"), (4, "MemCopy")]);
    }

    // ---------------------------------------------------------------------
    // Round 2 of the adversarial verifier's measurements against trust-cg
    // 0290f5153: each fixture below scanned clean there (scanned=1,
    // diagnostics=[], unknown=[], coverage_errors=0).
    // ---------------------------------------------------------------------

    fn target_info(triple: &str, pointer_size: u32) -> trust_ir::TargetInfo {
        trust_ir::TargetInfo {
            triple: triple.to_string(),
            pointer_size,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::default(),
        }
    }

    /// The result a declaration of `name` states for trust-cg-lower to read
    /// a call of it by its name (`classify_adapter_direct_call`): the C
    /// library's `memcpy`, `memmove` and `memset` return their destination
    /// (with `memset`'s `int` fill, [`c_memset_params`]), and
    /// `llvm.objectsize.i64.p0` an `i64`. Every other name here, LLVM's
    /// memory intrinsics among them, returns nothing.
    fn library_returns(name: &str) -> Vec<Ty> {
        match name {
            "memcpy" | "memmove" | "memset" => vec![Ty::Ptr],
            "llvm.objectsize.i64.p0" => vec![Ty::I64],
            _ => vec![],
        }
    }

    /// Append a body-less `External` declaration and return its id.
    fn declare(module: &mut Module, name: &str, params: Vec<Ty>) -> FuncId {
        let ty = FuncTyId::new(module.func_types.len() as u32);
        module.func_types.push(FuncTy {
            params,
            returns: library_returns(name),
            abi: None,
            is_vararg: false,
        });
        let id = FuncId::new(module.functions.len() as u32);
        module
            .functions
            .push(Function::new(id, name, ty, BlockId::new(0)));
        id
    }

    fn call(callee: FuncId, args: &[u32]) -> InstrNode {
        InstrNode::new(Inst::Call {
            callee,
            args: args.iter().copied().map(v).collect(),
        })
    }

    /// Only the reports about the function under test (`test`): body-less
    /// declarations are reported as skipped in their own right.
    fn test_skips(report: &super::FsymTrustIrReport) -> Vec<&super::FsymTrustIrSkip> {
        report
            .skipped_functions
            .iter()
            .filter(|skip| skip.function == "test")
            .collect()
    }

    fn unknown_kinds(report: &super::FsymTrustIrReport) -> Vec<FsymTrustIrDiagnosticKind> {
        report
            .unknown_obligations
            .iter()
            .map(|unknown| unknown.kind)
            .collect()
    }

    /// `test` calls declared function #1 (`name(params)`) with `body` built
    /// before the call.
    fn scan_call(
        name: &str,
        params: Vec<Ty>,
        mut body: Vec<InstrNode>,
        args: &[u32],
    ) -> super::FsymTrustIrReport {
        let mut site = call(FuncId::new(1), args);
        if !library_returns(name).is_empty() {
            site = site.with_result(v(98));
        }
        body.push(site);
        body.push(const_i64(99, 0));
        body.push(ret_i64(99));
        let mut module = test_module("fsym_named_call", body);
        assert_eq!(declare(&mut module, name, params), FuncId::new(1));
        scan_module(&module)
    }

    /// `llvm.memset`'s `(ptr, i8, size)`.
    fn memset_params() -> Vec<Ty> {
        vec![Ty::Ptr, Ty::U8, Ty::U64]
    }

    /// C's `memset(void *, int, size_t)` (its result is [`library_returns`]).
    fn c_memset_params() -> Vec<Ty> {
        vec![Ty::Ptr, Ty::I32, Ty::U64]
    }

    /// The fill parameters `symbol` takes: C's `int` for `memset`, LLVM's `i8`
    /// for its intrinsic.
    fn memset_params_for(symbol: &str) -> Vec<Ty> {
        if symbol == "memset" {
            c_memset_params()
        } else {
            memset_params()
        }
    }

    /// A zero fill operand of the type [`memset_params_for`] gives `symbol`.
    fn zero_fill_for(symbol: &str, result: u32) -> InstrNode {
        if symbol == "memset" {
            const_i32(result, 0)
        } else {
            const_u8(result, 0)
        }
    }

    fn const_i32(result: u32, value: i32) -> InstrNode {
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(value.into()),
        })
        .with_result(v(result))
    }

    fn memcpy_params() -> Vec<Ty> {
        vec![Ty::Ptr, Ty::Ptr, Ty::U64]
    }

    #[test]
    fn named_memset_call_through_null_reports_null_deref() {
        // Measured: `call @memset(null, 0u8, 8u64)` scanned clean.
        let report = scan_call(
            "memset",
            c_memset_params(),
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                const_i32(1, 0),
                const_u64(2, 8),
            ],
            &[0, 1, 2],
        );
        assert_eq!(report.scanned_functions, 1);
        assert!(report.coverage_errors.is_empty());
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::NullDeref]
        );
        assert_eq!(report.diagnostics[0].inst_index, 3);
        assert!(
            report.diagnostics[0].message.contains("memset destination"),
            "{}",
            report.diagnostics[0].message
        );
    }

    #[test]
    fn every_bulk_memory_symbol_is_checked_as_a_bulk_access() {
        for (symbol, kind) in super::BULK_MEMORY_SYMBOLS {
            let copies = *kind != super::BulkCallKind::Memset;
            let params = if copies {
                memcpy_params()
            } else {
                memset_params_for(symbol)
            };
            let (body, args): (Vec<InstrNode>, &[u32]) = if copies {
                (
                    vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(0)),
                        const_u64(2, 8),
                    ],
                    &[0, 0, 2],
                )
            } else {
                (
                    vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(0)),
                        zero_fill_for(symbol, 1),
                        const_u64(2, 8),
                    ],
                    &[0, 1, 2],
                )
            };
            let report = scan_call(symbol, params.clone(), body, args);
            assert!(report.coverage_errors.is_empty(), "{symbol}");
            let expected = if copies {
                vec![
                    FsymTrustIrDiagnosticKind::NullDeref,
                    FsymTrustIrDiagnosticKind::NullDeref,
                ]
            } else {
                vec![FsymTrustIrDiagnosticKind::NullDeref]
            };
            assert_eq!(diagnostic_kinds(&report), expected, "{symbol}");

            // In-bounds control: an 8-byte access to 8-byte allocas is clean.
            let (body, args): (Vec<InstrNode>, &[u32]) = if copies {
                (
                    vec![alloca_i64(0), alloca_i64(1), const_u64(2, 8)],
                    &[0, 1, 2],
                )
            } else {
                (
                    vec![alloca_i64(0), zero_fill_for(symbol, 1), const_u64(2, 8)],
                    &[0, 1, 2],
                )
            };
            let report = scan_call(symbol, params.clone(), body, args);
            assert!(
                report.diagnostics.is_empty(),
                "{symbol}: {:?}",
                report.diagnostics
            );
            assert!(
                report.unknown_obligations.is_empty(),
                "{symbol}: {:?}",
                report.unknown_obligations
            );

            // Oversized: 64 bytes into an 8-byte object.
            let (body, args): (Vec<InstrNode>, &[u32]) = if copies {
                (
                    vec![alloca_i64(0), alloca_i64(1), const_u64(2, 64)],
                    &[0, 1, 2],
                )
            } else {
                (
                    vec![alloca_i64(0), zero_fill_for(symbol, 1), const_u64(2, 64)],
                    &[0, 1, 2],
                )
            };
            let report = scan_call(symbol, params, body, args);
            assert!(
                diagnostic_kinds(&report)
                    .iter()
                    .all(|kind| *kind == FsymTrustIrDiagnosticKind::OutOfBounds)
                    && !report.diagnostics.is_empty(),
                "{symbol}: {:?}",
                report.diagnostics
            );
        }
    }

    #[test]
    fn bulk_memory_symbols_match_the_lowering() {
        use trust_cg_lower::adapter::{AdapterNamedCallSemantics, classify_adapter_named_call};
        for (symbol, kind) in super::BULK_MEMORY_SYMBOLS {
            let lowered = match kind {
                super::BulkCallKind::Memset => AdapterNamedCallSemantics::Memset,
                super::BulkCallKind::Memcpy => AdapterNamedCallSemantics::Memcpy,
                super::BulkCallKind::Memmove => AdapterNamedCallSemantics::Memmove,
            };
            assert_eq!(classify_adapter_named_call(symbol), lowered, "{symbol}");
        }
    }

    #[test]
    fn named_memcpy_overlap_is_ub_and_memmove_overlap_is_not() {
        let body = || {
            let mut body = alloca_i64_array4(0, 1);
            body.extend([const_i64(2, 8), byte_gep(3, 1, 2), const_u64(4, 16)]);
            body
        };
        for symbol in ["memcpy", "llvm.memcpy.p0.p0.i64"] {
            // dst [8, 24) and src [0, 16) of one 32-byte object.
            let report = scan_call(symbol, memcpy_params(), body(), &[3, 1, 4]);
            assert_eq!(
                diagnostic_kinds(&report),
                vec![FsymTrustIrDiagnosticKind::Overlap],
                "{symbol}"
            );
            assert!(report.diagnostics[0].message.contains(symbol));
        }
        for symbol in ["memmove", "llvm.memmove.p0.p0.i64"] {
            let report = scan_call(symbol, memcpy_params(), body(), &[3, 1, 4]);
            assert!(
                report.diagnostics.is_empty(),
                "{symbol}: {:?}",
                report.diagnostics
            );
            assert!(report.unknown_obligations.is_empty(), "{symbol}");
        }
    }

    #[test]
    fn named_memset_after_free_reports_use_after_free() {
        let report = scan_call(
            "memset",
            c_memset_params(),
            vec![
                heap_i64(0),
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
                const_i32(1, 0),
                const_u64(2, 8),
            ],
            &[0, 1, 2],
        );
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::UseAfterFree]
        );
    }

    #[test]
    fn module_local_body_named_memset_is_an_ordinary_call() {
        // trust-cg-lower binds a bodied Internal callee to its own body even
        // when its name spells `memset`; its accesses are its own scan's.
        let mut module = test_module(
            "fsym_local_memset",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                const_i32(1, 0),
                const_u64(2, 8),
                call(FuncId::new(1), &[0, 1, 2]).with_result(v(98)),
                const_i64(99, 0),
                ret_i64(99),
            ],
        );
        let id = declare(&mut module, "memset", c_memset_params());
        let local = module.function_by_id_mut(id).unwrap();
        local.linkage = trust_ir::Linkage::Internal;
        local.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::I32), (v(2), Ty::U64)],
            body: vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
        }];
        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 2);
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn a_library_name_declared_otherwise_is_scanned_as_an_external_call() {
        // trust-cg-lower lowers a call of `memset` declared otherwise than C's
        // (here LLVM's `i8` fill under the plain name) as an ordinary call of
        // whatever the link calls `memset`, so fsym scans it as that call: the
        // null destination it is handed is unsummarized, not a bulk write
        // through null (which the C prototype's call reports above).
        let report = scan_call(
            "memset",
            memset_params(),
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                const_u8(1, 0),
                const_u64(2, 8),
            ],
            &[0, 1, 2],
        );
        assert_eq!(report.scanned_functions, 1);
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
        assert_eq!(
            unknown_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::UnsummarizedCall]
        );
        // `n1_memcpy_ints`: integers only, so nothing is handed a pointer.
        let report = scan_call(
            "memcpy",
            vec![Ty::I64, Ty::I64, Ty::I64],
            vec![const_i64(0, 3), const_i64(1, 4), const_i64(2, 8)],
            &[0, 1, 2],
        );
        assert_eq!(report.scanned_functions, 1);
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
        assert!(
            report.unknown_obligations.is_empty(),
            "{:?}",
            report.unknown_obligations
        );
    }

    #[test]
    fn external_call_handed_a_pointer_is_an_unsummarized_unknown() {
        let report = scan_call("sink", vec![Ty::Ptr], vec![alloca_i64(0)], &[0]);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.diagnostics.is_empty());
        assert!(report.coverage_errors.is_empty());
        assert_eq!(
            unknown_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::UnsummarizedCall]
        );
        let unknown = &report.unknown_obligations[0];
        assert!(unknown.reason.contains("`sink`"), "{}", unknown.reason);
        assert!(unknown.solver_candidate.is_none());

        // A pointer inside an aggregate, and a variadic tail, count too.
        let mut module = test_module(
            "fsym_variadic_call",
            vec![
                alloca_i64(0),
                const_i64(1, 7),
                call(FuncId::new(1), &[1, 0]),
                const_i64(99, 0),
                ret_i64(99),
            ],
        );
        declare(&mut module, "printf_like", vec![Ty::I64]);
        let report = scan_module(&module);
        assert_eq!(
            unknown_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::UnsummarizedCall]
        );
        assert!(report.unknown_obligations[0].reason.contains("#1"));
    }

    #[test]
    fn external_call_with_only_scalar_arguments_is_clean() {
        let report = scan_call(
            "compute",
            vec![Ty::I64, Ty::F64, Ty::Bool],
            vec![
                const_i64(0, 1),
                InstrNode::new(Inst::Const {
                    ty: Ty::F64,
                    value: Constant::Float(1.0),
                })
                .with_result(v(1)),
                const_bool(2, true),
            ],
            &[0, 1, 2],
        );
        assert_eq!(report.scanned_functions, 1);
        assert!(report.diagnostics.is_empty());
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn replaceable_or_unresolved_callee_is_an_unsummarized_unknown() {
        // A weak definition may be replaced at link time by another body.
        let mut module = test_module(
            "fsym_weak_callee",
            vec![
                alloca_i64(0),
                call(FuncId::new(1), &[0]),
                const_i64(99, 0),
                ret_i64(99),
            ],
        );
        let id = declare(&mut module, "weak_sink", vec![Ty::Ptr]);
        let weak = module.function_by_id_mut(id).unwrap();
        weak.linkage = trust_ir::Linkage::Weak;
        weak.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![InstrNode::new(Inst::Return { values: vec![] })],
        }];
        let report = scan_module(&module);
        assert!(
            report.unknown_obligations.iter().any(|unknown| {
                unknown.kind == FsymTrustIrDiagnosticKind::UnsummarizedCall
                    && unknown.function == "test"
            }),
            "{:?}",
            report.unknown_obligations
        );

        // A callee id the module does not define.
        let report = scan_body("fsym_unresolved_callee", vec![call(FuncId::new(42), &[])]);
        assert_eq!(report.scanned_functions, 1);
        assert_eq!(
            unknown_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::UnsummarizedCall]
        );
        assert!(report.unknown_obligations[0].reason.contains("f42"));
    }

    /// fsym binds a call to a callee's body only when the link cannot replace
    /// it (`callee_binds_to_module_body`): a bodied `External` / `Internal` /
    /// `Private` callee. That is deliberately narrower than trust-ir's proved
    /// `!Linkage::is_interposable()`, which also binds `WeakOdr` /
    /// `LinkOnceOdr` / `AvailableExternally` under the one-definition-rule
    /// premise trust-ir discloses and does not verify. Each of the nine
    /// linkages is driven through a real call that hands the callee a
    /// pointer, so adopting the premise (collapsing the predicate onto the
    /// proved table) turns the three ODR rows Safe and this test red.
    #[test]
    fn a_callee_the_link_may_replace_is_unsummarized_even_under_the_odr_premise() {
        use trust_ir::Linkage;
        let linkages = [
            Linkage::External,
            Linkage::Internal,
            Linkage::Private,
            Linkage::Weak,
            Linkage::LinkOnce,
            Linkage::AvailableExternally,
            Linkage::ExternalWeak,
            Linkage::WeakOdr,
            Linkage::LinkOnceOdr,
        ];
        let mut odr_premise_rows = Vec::new();
        for linkage in linkages {
            // fsym's own table, stated independently and exhaustively.
            let link_may_replace = match linkage {
                Linkage::External | Linkage::Internal | Linkage::Private => false,
                Linkage::Weak
                | Linkage::LinkOnce
                | Linkage::AvailableExternally
                | Linkage::ExternalWeak
                | Linkage::WeakOdr
                | Linkage::LinkOnceOdr => true,
            };
            if link_may_replace != linkage.is_interposable() {
                odr_premise_rows.push(linkage);
            }

            let mut module = test_module(
                "fsym_callee_linkage",
                vec![
                    alloca_i64(0),
                    call(FuncId::new(1), &[0]),
                    const_i64(99, 0),
                    ret_i64(99),
                ],
            );
            let id = declare(&mut module, "sink", vec![Ty::Ptr]);
            let callee = module.function_by_id_mut(id).unwrap();
            callee.linkage = linkage;
            callee.blocks = vec![Block {
                id: BlockId::new(0),
                params: vec![(v(0), Ty::Ptr)],
                body: vec![InstrNode::new(Inst::Return { values: vec![] })],
            }];
            let report = scan_module(&module);
            assert!(
                report.diagnostics.is_empty(),
                "{linkage:?}: {:?}",
                report.diagnostics
            );
            let caller_unknowns: Vec<_> = report
                .unknown_obligations
                .iter()
                .filter(|unknown| unknown.function == "test")
                .collect();
            if link_may_replace {
                assert_eq!(caller_unknowns.len(), 1, "{linkage:?}: {caller_unknowns:?}");
                let unknown = caller_unknowns[0];
                assert_eq!(
                    unknown.kind,
                    FsymTrustIrDiagnosticKind::UnsummarizedCall,
                    "{linkage:?}"
                );
                assert!(
                    unknown.reason.contains("link-replaceable callee `sink`"),
                    "{linkage:?}: {}",
                    unknown.reason
                );
            } else {
                // The callee's body is this module's and is scanned in its
                // own right: the call itself owes nothing further.
                assert!(
                    caller_unknowns.is_empty(),
                    "{linkage:?}: {caller_unknowns:?}"
                );
            }
        }
        // The difference from trust-ir's proved interposition table is exactly
        // the one-definition-rule premise fsym does not take.
        assert_eq!(
            odr_premise_rows,
            [
                Linkage::AvailableExternally,
                Linkage::WeakOdr,
                Linkage::LinkOnceOdr
            ]
        );
    }

    #[test]
    fn value_only_intrinsic_call_touches_no_memory() {
        let report = scan_call(
            "llvm.objectsize.i64.p0",
            vec![Ty::Ptr, Ty::Bool, Ty::Bool, Ty::Bool],
            vec![
                alloca_i64(0),
                const_bool(1, false),
                const_bool(2, true),
                const_bool(3, false),
            ],
            &[0, 1, 2, 3],
        );
        assert_eq!(report.scanned_functions, 1);
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn unlisted_bulk_lowering_and_wrong_arity_are_refused_by_name() {
        // The lowering treats every `llvm.memcpy*` name as a copy; fsym
        // checks only the names it lists.
        let report = scan_call(
            "llvm.memcpy.p0.p0.i16",
            memcpy_params(),
            vec![alloca_i64(0), alloca_i64(1), const_u64(2, 8)],
            &[0, 1, 2],
        );
        assert_eq!(report.scanned_functions, 0);
        let skips = test_skips(&report);
        assert_eq!(
            skips[0].reason,
            FsymTrustIrSkipReason::UnsupportedInstruction
        );
        assert!(skips[0].detail.contains("llvm.memcpy.p0.p0.i16"));

        // A volatile flag the importer would have stripped.
        let report = scan_call(
            "llvm.memset.p0.i64",
            vec![Ty::Ptr, Ty::U8, Ty::U64, Ty::Bool],
            vec![
                alloca_i64(0),
                const_u8(1, 0),
                const_u64(2, 8),
                const_bool(3, false),
            ],
            &[0, 1, 2, 3],
        );
        assert_eq!(report.scanned_functions, 0);
        // trust-cg-lower refuses that declaration by name (it is not LLVM's
        // type as the importer states it), and fsym with it.
        let detail = &test_skips(&report)[0].detail;
        assert!(
            detail.contains("[TCG-NAMED-CALL-PROTOTYPE]") && detail.contains("llvm.memset.p0.i64"),
            "{detail}"
        );
    }

    #[test]
    fn call_obligations_are_coverage_sites() {
        let mut module = test_module(
            "fsym_call_coverage",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                const_i32(1, 0),
                const_u64(2, 8),
                call(FuncId::new(1), &[0, 1, 2]).with_result(v(98)),
                call(FuncId::new(2), &[0]),
                const_i64(3, 0),
                ret_i64(3),
            ],
        );
        declare(&mut module, "memset", c_memset_params());
        declare(&mut module, "sink", vec![Ty::Ptr]);
        let function = &module.functions[0];
        let block = &function.blocks[0];
        assert_eq!(
            site_opcodes(super::reachable_obligation_sites(&module, block)),
            vec![(3, "memset"), (4, "Call")]
        );
        let mut dropped = FunctionScan::new(&module, function, block, TARGET_64);
        dropped.force_drop_deref = true;
        dropped.run_block();
        // One coverage error per dropped obligation class; one row per site.
        let mut opcodes: Vec<_> = dropped
            .coverage_errors
            .iter()
            .map(|error| (error.inst_index, error.opcode))
            .collect();
        opcodes.dedup();
        assert_eq!(opcodes, vec![(3, "memset")]);
    }

    /// bb0 branches on `icmp eq (load u64 from alloca), 0`: a condition with
    /// no modeled value. bb1 holds `then_body`, bb2 returns.
    fn unmodeled_branch_module(name: &str, then_body: Vec<InstrNode>) -> Module {
        let mut then_body = then_body;
        then_body.push(const_i64(19, 0));
        then_body.push(ret_i64(19));
        test_module_blocks(
            name,
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        alloca_i64(0),
                        init_slot(0, 8)[0].clone(),
                        init_slot(0, 8)[1].clone(),
                        InstrNode::new(Inst::Load {
                            ty: Ty::U64,
                            ptr: v(0),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(1)),
                        const_u64(2, 0),
                        InstrNode::new(Inst::ICmp {
                            op: ICmpOp::Eq,
                            ty: Ty::U64,
                            lhs: v(1),
                            rhs: v(2),
                        })
                        .with_result(v(3)),
                        condbr(3, 1, &[], 2, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: then_body,
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![const_i64(29, 0), ret_i64(29)],
                },
            ],
        )
    }

    #[test]
    fn unmodeled_branch_condition_still_walks_both_arms() {
        // Measured: a null 8-byte MemSet, or a null Store, in bb1 scanned
        // clean because bb1 was never walked.
        for (label, then_body) in [
            (
                "memset",
                vec![
                    InstrNode::new(Inst::NullPtr).with_result(v(10)),
                    const_u8(11, 0),
                    const_u64(12, 8),
                    memset(10, 11, 12),
                ],
            ),
            (
                "store",
                vec![
                    InstrNode::new(Inst::NullPtr).with_result(v(10)),
                    const_i64(11, 0),
                    InstrNode::new(Inst::Store {
                        ty: Ty::I64,
                        ptr: v(10),
                        value: v(11),
                        volatile: false,
                        align: None,
                    }),
                ],
            ),
        ] {
            let report = scan_module(&unmodeled_branch_module("fsym_unmodeled_branch", then_body));
            assert_eq!(report.scanned_functions, 1, "{label}");
            assert!(report.coverage_errors.is_empty(), "{label}");
            // UB whenever bb1 is reached, but nothing establishes that it is:
            // an Unknown naming the branch, never a pass and never escalated.
            assert!(
                report.diagnostics.is_empty(),
                "{label}: {:?}",
                report.diagnostics
            );
            let null = report
                .unknown_obligations
                .iter()
                .find(|unknown| {
                    unknown.kind == FsymTrustIrDiagnosticKind::NullDeref && unknown.block == 1
                })
                .unwrap_or_else(|| panic!("{label}: {:?}", report.unknown_obligations));
            assert!(
                null.reason.contains("bb0 CondBr condition v3"),
                "{}",
                null.reason
            );
            assert!(null.solver_candidate.is_none());
        }
    }

    #[test]
    fn unmodeled_branch_arms_keep_proven_safety_and_reach_the_join() {
        // An in-bounds access in an arm stays Safe, and a join block after
        // the diamond is walked on both paths.
        let module = test_module_blocks(
            "fsym_unmodeled_join",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        alloca_i64(0),
                        init_slot(0, 8)[0].clone(),
                        init_slot(0, 8)[1].clone(),
                        InstrNode::new(Inst::Load {
                            ty: Ty::Bool,
                            ptr: v(0),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(1)),
                        condbr(1, 1, &[], 2, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        const_i64(10, 1),
                        InstrNode::new(Inst::Store {
                            ty: Ty::I64,
                            ptr: v(0),
                            value: v(10),
                            volatile: false,
                            align: None,
                        }),
                        br(3, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![br(3, &[])],
                },
                Block {
                    id: BlockId::new(3),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(30)),
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(30),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(31)),
                        ret_i64(31),
                    ],
                },
            ],
        );
        let report = scan_module(&module);
        assert!(report.coverage_errors.is_empty());
        assert!(
            report
                .unknown_obligations
                .iter()
                .all(|unknown| unknown.block == 3),
            "{:?}",
            report.unknown_obligations
        );
        // Walked on both paths; the two paths' Unknowns are identical (an
        // unmodeled branch adds no path fact), so one is recorded.
        assert_eq!(
            report
                .unknown_obligations
                .iter()
                .filter(|unknown| unknown.kind == FsymTrustIrDiagnosticKind::NullDeref)
                .count(),
            1,
            "{:?}",
            report.unknown_obligations
        );
    }

    #[test]
    fn non_boolean_branch_condition_walks_both_arms() {
        // A condition of a sort the path condition cannot hold used to become
        // an unsatisfiable guard on BOTH arms, pruning them.
        let module = test_module_blocks(
            "fsym_non_bool_condition",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![const_u8(0, 1), condbr(0, 1, &[], 1, &[])],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(10)),
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(10),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(11)),
                        ret_i64(11),
                    ],
                },
            ],
        );
        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(
            unknown_kinds(&report).contains(&FsymTrustIrDiagnosticKind::NullDeref),
            "{report:?}"
        );
    }

    #[test]
    fn unmodeled_switch_selector_walks_every_arm() {
        let null_load_block = |id: u32| Block {
            id: BlockId::new(id),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::NullPtr).with_result(v(id * 10)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(id * 10),
                    volatile: false,
                    align: None,
                })
                .with_result(v(id * 10 + 1)),
                ret_i64(id * 10 + 1),
            ],
        };
        let module = test_module_blocks(
            "fsym_unmodeled_switch",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        alloca_i64(0),
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(0),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(1)),
                        InstrNode::new(Inst::Switch {
                            value: v(1),
                            default: BlockId::new(3),
                            default_args: vec![],
                            cases: vec![
                                SwitchCase {
                                    value: Constant::Int(0),
                                    target: BlockId::new(1),
                                    args: vec![],
                                },
                                SwitchCase {
                                    value: Constant::Int(1),
                                    target: BlockId::new(2),
                                    args: vec![],
                                },
                            ],
                            exhaustive_enum_unreachable: false,
                        }),
                    ],
                },
                null_load_block(1),
                null_load_block(2),
                null_load_block(3),
            ],
        );
        let report = scan_module(&module);
        assert_eq!(
            report.scanned_functions, 1,
            "{:?}",
            report.skipped_functions
        );
        let mut blocks: Vec<_> = report
            .unknown_obligations
            .iter()
            .filter(|unknown| unknown.kind == FsymTrustIrDiagnosticKind::NullDeref)
            .map(|unknown| unknown.block)
            .collect();
        blocks.sort_unstable();
        assert_eq!(blocks, vec![1, 2, 3]);
        assert!(report.diagnostics.is_empty());
    }

    #[test]
    fn loop_reached_only_through_an_unmodeled_branch_is_validated() {
        // bb0's condition is loaded; the loop behind it has no static trip
        // count (the bound is a parameter). Validation used to drop bb0's
        // successors, never see the loop, and admit the function; the walk
        // dropped them too, so the function scanned clean.
        let module = test_module_blocks(
            "fsym_loop_behind_unmodeled_branch",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![(v(90), Ty::I64)],
                    body: vec![
                        alloca_i64(0),
                        InstrNode::new(Inst::Load {
                            ty: Ty::Bool,
                            ptr: v(0),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(1)),
                        const_i64(2, 0),
                        condbr(1, 1, &[2], 3, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![(v(10), Ty::I64)],
                    body: vec![
                        icmp_i64(11, ICmpOp::Slt, 10, 90),
                        condbr(11, 2, &[], 3, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        const_i64(20, 1),
                        bin_i64(21, BinOp::Add, 10, 20),
                        br(1, &[21]),
                    ],
                },
                Block {
                    id: BlockId::new(3),
                    params: vec![],
                    body: vec![const_i64(30, 0), ret_i64(30)],
                },
            ],
        );
        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::Loop
        );
    }

    fn usize_const(result: u32, value: i128) -> InstrNode {
        InstrNode::new(Inst::Const {
            ty: Ty::Usize,
            value: Constant::Int(value),
        })
        .with_result(v(result))
    }

    fn scan_pinned(
        name: &str,
        target: Option<trust_ir::TargetInfo>,
        mut body: Vec<InstrNode>,
    ) -> super::FsymTrustIrReport {
        body.push(const_i64(99, 0));
        body.push(ret_i64(99));
        let mut module = test_module(name, body);
        module.target_info = target;
        scan_module(&module)
    }

    #[test]
    fn usize_and_isize_arithmetic_ub_is_checked_at_the_target_width() {
        // Measured: `udiv usize 8, 0` scanned clean (`udiv u64 8, 0` did not).
        let udiv = vec![
            usize_const(0, 8),
            usize_const(1, 0),
            InstrNode::new(Inst::BinOp {
                op: BinOp::UDiv,
                ty: Ty::Usize,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        ];
        for target in [
            target_info("aarch64-apple-darwin", 8),
            target_info("wasm32-unknown-unknown", 4),
        ] {
            let report = scan_pinned("fsym_udiv_usize", Some(target.clone()), udiv.clone());
            assert_eq!(
                diagnostic_kinds(&report),
                vec![FsymTrustIrDiagnosticKind::Arithmetic],
                "{}",
                target.triple
            );
        }
        let report = scan_pinned("fsym_udiv_usize_target_free", None, udiv);
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::PointerWidth
        );

        // `isize::MIN / -1` overflows only at the target's width.
        let sdiv = |min: i128| {
            vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Isize,
                    value: Constant::Int(min),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Const {
                    ty: Ty::Isize,
                    value: Constant::Int(-1),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::SDiv,
                    ty: Ty::Isize,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
            ]
        };
        let wasm = Some(target_info("wasm32-unknown-unknown", 4));
        let native = Some(target_info("aarch64-apple-darwin", 8));
        let report = scan_pinned("fsym_sdiv_isize32", wasm, sdiv(i128::from(i32::MIN)));
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::Arithmetic]
        );
        let report = scan_pinned("fsym_sdiv_isize64", native, sdiv(i128::from(i32::MIN)));
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn unmodelable_arithmetic_is_an_unknown_never_a_pass() {
        // A divisor loaded from memory, a 128-bit division, and a lane-wise
        // vector division each owe a verdict the scanner cannot compute.
        let loaded = scan_body(
            "fsym_udiv_loaded",
            vec![
                alloca_i64(0),
                init_slot(0, 8)[0].clone(),
                init_slot(0, 8)[1].clone(),
                InstrNode::new(Inst::Load {
                    ty: Ty::U64,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                })
                .with_result(v(1)),
                const_u64(2, 8),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::UDiv,
                    ty: Ty::U64,
                    lhs: v(2),
                    rhs: v(1),
                })
                .with_result(v(3)),
            ],
        );
        let wide = scan_body(
            "fsym_udiv_u128",
            vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::U128,
                    value: Constant::Int(8),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Const {
                    ty: Ty::U128,
                    value: Constant::Int(0),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::UDiv,
                    ty: Ty::U128,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
            ],
        );
        for report in [loaded, wide] {
            assert_eq!(report.scanned_functions, 1);
            assert!(report.coverage_errors.is_empty());
            assert_eq!(
                unknown_kinds(&report),
                vec![FsymTrustIrDiagnosticKind::Arithmetic],
                "{report:?}"
            );
        }
    }

    #[test]
    fn arithmetic_ub_sites_are_coverage_sites() {
        let module = test_module(
            "fsym_arith_coverage",
            vec![
                const_i64(0, 8),
                const_i64(1, 2),
                bin_i64(2, BinOp::SDiv, 0, 1),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::U64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(3)),
                ret_i64(2),
            ],
        );
        let block = &module.functions[0].blocks[0];
        assert_eq!(
            site_opcodes(super::reachable_obligation_sites(&module, block)),
            vec![(2, "BinOp")]
        );
    }

    #[test]
    fn usize_select_count_is_modeled_at_the_target_pointer_width() {
        // Measured: with pointer_size = 4,
        // `count = select((usize 0xFFFF_FFFF + 1) == 0, 8, 0)` evaluated to 0
        // at an assumed 64 bits, so a null MemSet was recorded Safe; on the
        // target the count is 8.
        let body = vec![
            usize_const(0, 0xFFFF_FFFF),
            usize_const(1, 1),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::Usize,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
            usize_const(3, 0),
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::Usize,
                lhs: v(2),
                rhs: v(3),
            })
            .with_result(v(4)),
            usize_const(5, 8),
            InstrNode::new(Inst::Select {
                ty: Ty::Usize,
                cond: v(4),
                then_val: v(5),
                else_val: v(3),
            })
            .with_result(v(6)),
            InstrNode::new(Inst::NullPtr).with_result(v(7)),
            const_u8(8, 0),
            memset(7, 8, 6),
        ];
        let report = scan_pinned(
            "fsym_usize_wrap32",
            Some(target_info("wasm32-unknown-unknown", 4)),
            body.clone(),
        );
        assert_eq!(report.scanned_functions, 1);
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::NullDeref]
        );

        // Control: at 8-byte pointers the sum is 2^32 and the count is 0 — a
        // defined zero-byte no-op.
        let report = scan_pinned(
            "fsym_usize_wrap64",
            Some(target_info("aarch64-apple-darwin", 8)),
            body.clone(),
        );
        assert_eq!(report.scanned_functions, 1);
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
        assert!(report.unknown_obligations.is_empty());

        // 4-byte pointers without a layout table fsym models, and a pointer
        // width no backend has, are refused by name.
        for target in [
            target_info("i686-unknown-linux-gnu", 4),
            target_info("avr-unknown-unknown", 2),
        ] {
            let report = scan_pinned("fsym_unmodeled_target", Some(target.clone()), body.clone());
            assert_eq!(report.scanned_functions, 0, "{}", target.triple);
            assert_eq!(
                report.skipped_functions[0].reason,
                FsymTrustIrSkipReason::PointerWidth
            );
            assert!(report.skipped_functions[0].detail.contains(&target.triple));
        }
    }

    #[test]
    fn object_sizes_follow_the_target_layout() {
        // A pointer slot is 4 bytes on wasm32: an 8-byte load from it is out
        // of bounds there, in bounds at 8-byte pointers.
        let body = vec![
            InstrNode::new(Inst::Alloca {
                ty: Ty::Ptr,
                count: None,
                align: None,
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(1)),
        ];
        let report = scan_pinned(
            "fsym_ptr_slot32",
            Some(target_info("wasm32-unknown-unknown", 4)),
            body.clone(),
        );
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
        let report = scan_pinned(
            "fsym_ptr_slot64",
            Some(target_info("aarch64-apple-darwin", 8)),
            body,
        );
        assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
    }

    #[test]
    fn scan_function_in_module_resolves_callees_from_the_module() {
        let mut module = test_module(
            "fsym_scan_one",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                const_i32(1, 0),
                const_u64(2, 8),
                call(FuncId::new(1), &[0, 1, 2]).with_result(v(98)),
                const_i64(99, 0),
                ret_i64(99),
            ],
        );
        declare(&mut module, "memset", c_memset_params());
        let report = super::scan_function_in_module(&module, &module.functions[0]);
        assert_eq!(report.scanned_function_names, vec!["test".to_string()]);
        assert!(report.skipped_functions.is_empty());
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::NullDeref]
        );
    }

    // ---------------------------------------------------------------------
    // Round 3: the abstract pointer model, and the UB classes it was silent on.
    // Each test pins the verdict KIND the review's measured case now gets;
    // `tests/fsym_interpreter_oracle.rs` checks the same cases (and a seeded
    // generated corpus) against trust-ir's reference interpreter.
    // ---------------------------------------------------------------------

    fn node(result: u32, inst: Inst) -> InstrNode {
        InstrNode::new(inst).with_result(v(result))
    }

    fn u8_alloca(result: u32, count: Option<u32>, align: Option<u64>) -> InstrNode {
        node(
            result,
            Inst::Alloca {
                ty: Ty::U8,
                count: count.map(v),
                align,
            },
        )
    }

    fn cast(result: u32, op: trust_ir::CastOp, src_ty: Ty, dst_ty: Ty, operand: u32) -> InstrNode {
        node(
            result,
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand: v(operand),
            },
        )
    }

    fn ptrtoint(result: u32, ptr: u32) -> InstrNode {
        cast(result, trust_ir::CastOp::PtrToInt, Ty::Ptr, Ty::U64, ptr)
    }

    fn u64_bin(result: u32, op: BinOp, lhs: u32, rhs: u32) -> InstrNode {
        node(
            result,
            Inst::BinOp {
                op,
                ty: Ty::U64,
                lhs: v(lhs),
                rhs: v(rhs),
            },
        )
    }

    fn store_u8(ptr: u32, value: u32) -> InstrNode {
        InstrNode::new(Inst::Store {
            ty: Ty::U8,
            ptr: v(ptr),
            value: v(value),
            volatile: false,
            align: None,
        })
    }

    fn load(result: u32, ty: Ty, ptr: u32, align: Option<u64>) -> InstrNode {
        node(
            result,
            Inst::Load {
                ty,
                ptr: v(ptr),
                volatile: false,
                align,
            },
        )
    }

    fn i64_gep(result: u32, pointee_ty: Ty, base: u32, index: u32) -> InstrNode {
        node(
            result,
            Inst::GEP {
                pointee_ty,
                base: v(base),
                indices: vec![v(index)],
                inbounds: false,
            },
        )
    }

    /// bb0 computes `cond` with `prefix`, then branches: bb1 returns, bb2 (the
    /// arm taken at run time) stores through null.
    fn branch_on(prefix: Vec<InstrNode>, cond: u32) -> super::FsymTrustIrReport {
        let mut entry = prefix;
        entry.push(condbr(cond, 1, &[], 2, &[]));
        scan_module(&test_module_blocks(
            "fsym_abstract_branch",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: entry,
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![const_i64(10, 0), ret_i64(10)],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(20)),
                        const_u8(21, 0),
                        store_u8(20, 21),
                        const_i64(22, 0),
                        ret_i64(22),
                    ],
                },
            ],
        ))
    }

    #[test]
    fn pointer_comparisons_check_both_operand_addresses() {
        let compare = |ty| {
            node(
                3,
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty,
                    lhs: v(0),
                    rhs: v(1),
                },
            )
        };
        // Check each operand independently: two identical Unknown records
        // at the same site are intentionally deduplicated by scan_function.
        // A one-sided checker must still fail one of the asymmetric cases.
        for (name, params, body) in [
            (
                "fsym_pointer_compare_unknown_lhs",
                vec![(v(0), Ty::Ptr)],
                vec![alloca_i64(1), compare(Ty::Ptr)],
            ),
            (
                "fsym_pointer_compare_unknown_rhs",
                vec![(v(1), Ty::Ptr)],
                vec![alloca_i64(0), compare(Ty::Ptr)],
            ),
            (
                "fsym_pointer_compare_parameters",
                vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
                vec![compare(Ty::Ptr)],
            ),
        ] {
            let report = scan_with_params(name, params, body);
            let address_debts: Vec<_> = unknown_kinds(&report)
                .into_iter()
                .filter(|kind| *kind == FsymTrustIrDiagnosticKind::PointerArithmetic)
                .collect();
            assert_eq!(
                address_debts,
                vec![FsymTrustIrDiagnosticKind::PointerArithmetic],
                "{name}"
            );
        }
        let integers = scan_with_params(
            "fsym_integer_compare_parameters",
            vec![(v(0), Ty::I64), (v(1), Ty::I64)],
            vec![compare(Ty::I64)],
        );
        assert!(!unknown_kinds(&integers).contains(&FsymTrustIrDiagnosticKind::PointerArithmetic));
        let tracked = scan_body(
            "fsym_pointer_compare_tracked",
            vec![alloca_i64(0), alloca_i64(1), compare(Ty::Ptr)],
        );
        assert!(!unknown_kinds(&tracked).contains(&FsymTrustIrDiagnosticKind::PointerArithmetic));
        assert!(
            !diagnostic_kinds(&tracked).contains(&FsymTrustIrDiagnosticKind::PointerArithmetic)
        );
        let module = test_module("fsym_compare_debts", vec![]);
        assert!(
            super::fsym_owed_kinds(&module, &compare(Ty::Ptr).inst)
                .contains(&FsymTrustIrDiagnosticKind::PointerArithmetic)
        );
        assert!(
            !super::fsym_owed_kinds(&module, &compare(Ty::I64).inst)
                .contains(&FsymTrustIrDiagnosticKind::PointerArithmetic)
        );
    }

    #[test]
    fn pointer_comparisons_on_tracked_objects_are_unmodeled_and_prune_nothing() {
        // Measured: `icmp eq (gep a, 1), a` was TRUE in the model (GEP kept
        // the object id as the "address"), so the ELSE arm — the one taken at
        // run time — was pruned and its null store never checked.
        let gep_vs_base = branch_on(
            vec![
                u8_alloca(0, None, None),
                const_i64(1, 1),
                i64_gep(2, Ty::U8, 0, 1),
                node(
                    3,
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::Ptr,
                        lhs: v(2),
                        rhs: v(0),
                    },
                ),
            ],
            3,
        );
        // Measured: `icmp ult a, b` was decided by object-id order.
        let object_order = branch_on(
            vec![
                u8_alloca(0, None, None),
                u8_alloca(1, None, None),
                node(
                    3,
                    Inst::ICmp {
                        op: ICmpOp::Ult,
                        ty: Ty::Ptr,
                        lhs: v(0),
                        rhs: v(1),
                    },
                ),
            ],
            3,
        );
        // The same comparison through `ptrtoint`: an abstract address is not
        // an integer.
        let through_ptrtoint = branch_on(
            vec![
                u8_alloca(0, None, None),
                const_i64(1, 1),
                i64_gep(2, Ty::U8, 0, 1),
                ptrtoint(4, 2),
                ptrtoint(5, 0),
                node(
                    3,
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::U64,
                        lhs: v(4),
                        rhs: v(5),
                    },
                ),
            ],
            3,
        );
        for report in [gep_vs_base, object_order, through_ptrtoint] {
            assert!(report.coverage_errors.is_empty());
            // Both arms walked with no path fact: the null store is UB if
            // reached, an Unknown naming the unmodeled branch.
            assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
            assert!(
                report
                    .unknown_obligations
                    .iter()
                    .any(|unknown| unknown.block == 2
                        && unknown.kind == FsymTrustIrDiagnosticKind::NullDeref
                        && unknown.reason.contains("unmodeled")),
                "{:?}",
                report.unknown_obligations
            );
        }
    }

    #[test]
    fn exact_addresses_still_decide_comparisons() {
        // `null == null` is exact: the ELSE arm is infeasible and pruned.
        let report = branch_on(
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                InstrNode::new(Inst::NullPtr).with_result(v(1)),
                node(
                    3,
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::Ptr,
                        lhs: v(0),
                        rhs: v(1),
                    },
                ),
            ],
            3,
        );
        assert!(report.diagnostics.is_empty());
        assert!(report.unknown_obligations.is_empty(), "{report:?}");
    }

    #[test]
    fn ptrtoint_of_a_tracked_object_is_not_a_value() {
        // Measured: `udiv 8, ptrtoint(alloca align 16) & 15` (run-time
        // divisor 0) and `udiv 8, ptrtoint(gep a, 1) - ptrtoint(a) - 1` both
        // folded the object id and scanned clean.
        let masked = scan_body(
            "fsym_ptrtoint_masked",
            vec![
                u8_alloca(0, None, Some(16)),
                ptrtoint(1, 0),
                const_u64(2, 15),
                u64_bin(3, BinOp::And, 1, 2),
                const_u64(4, 8),
                u64_bin(5, BinOp::UDiv, 4, 3),
            ],
        );
        let difference = scan_body(
            "fsym_ptrtoint_difference",
            vec![
                const_u64(9, 2),
                u8_alloca(0, Some(9), None),
                const_i64(1, 1),
                i64_gep(2, Ty::U8, 0, 1),
                ptrtoint(3, 2),
                ptrtoint(4, 0),
                u64_bin(5, BinOp::Sub, 3, 4),
                const_u64(6, 1),
                u64_bin(7, BinOp::Sub, 5, 6),
                const_u64(8, 8),
                u64_bin(10, BinOp::UDiv, 8, 7),
            ],
        );
        for report in [masked, difference] {
            assert!(report.diagnostics.is_empty());
            assert_eq!(
                unknown_kinds(&report),
                vec![FsymTrustIrDiagnosticKind::Arithmetic],
                "{:?}",
                report.unknown_obligations
            );
        }
    }

    #[test]
    fn inttoptr_and_constant_addresses_carry_no_provenance() {
        // Measured: a load through `inttoptr(ptrtoint(freed alloca))`, a
        // store through `inttoptr(ptrtoint(alloca u8) + 100)` and one through
        // the constant pointer 0x1000 were clean or only null-Unknown.
        let freed = scan_body(
            "fsym_inttoptr_freed",
            vec![
                heap_i64(0),
                ptrtoint(1, 0),
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
                cast(2, trust_ir::CastOp::IntToPtr, Ty::U64, Ty::Ptr, 1),
                load(3, Ty::I64, 2, None),
            ],
        );
        let moved = scan_body(
            "fsym_inttoptr_moved",
            vec![
                u8_alloca(0, None, None),
                ptrtoint(1, 0),
                const_u64(2, 100),
                u64_bin(3, BinOp::Add, 1, 2),
                cast(4, trust_ir::CastOp::IntToPtr, Ty::U64, Ty::Ptr, 3),
                const_u8(5, 1),
                store_u8(4, 5),
            ],
        );
        let constant = scan_body(
            "fsym_const_ptr",
            vec![
                node(
                    0,
                    Inst::Const {
                        ty: Ty::Ptr,
                        value: Constant::Int(0x1000),
                    },
                ),
                const_u8(1, 1),
                store_u8(0, 1),
            ],
        );
        for report in [freed, moved, constant] {
            assert!(report.coverage_errors.is_empty());
            assert!(
                unknown_kinds(&report).contains(&FsymTrustIrDiagnosticKind::OutOfBounds),
                "{:?}",
                report.unknown_obligations
            );
        }
    }

    #[test]
    fn gep_moves_the_exact_address_and_checks_its_arithmetic() {
        // Measured: `store u8, gep(const ptr 0xFFFF_FFFF_FFFF_FFF8, 8)`
        // writes address 0; the GEP kept the base's (nonzero) null model.
        let wrapping = scan_body(
            "fsym_gep_wraps",
            vec![
                node(
                    0,
                    Inst::Const {
                        ty: Ty::Ptr,
                        value: Constant::Int(0xFFFF_FFFF_FFFF_FFF8),
                    },
                ),
                const_i64(1, 8),
                i64_gep(2, Ty::U8, 0, 1),
                const_u8(3, 1),
                store_u8(2, 3),
            ],
        );
        assert!(
            diagnostic_kinds(&wrapping).contains(&FsymTrustIrDiagnosticKind::PointerArithmetic),
            "{wrapping:?}"
        );

        // A negative signed index is UB with no dereference at all.
        let negative = scan_body(
            "fsym_gep_negative",
            vec![
                const_u64(9, 4),
                u8_alloca(0, Some(9), None),
                const_i64(1, -1),
                i64_gep(2, Ty::U8, 0, 1),
            ],
        );
        assert_eq!(
            diagnostic_kinds(&negative),
            vec![FsymTrustIrDiagnosticKind::PointerArithmetic]
        );

        // A GEP on null is UB with no dereference at all.
        let null_base = scan_body(
            "fsym_gep_null",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                const_i64(1, 0),
                i64_gep(2, Ty::U8, 0, 1),
            ],
        );
        assert_eq!(
            diagnostic_kinds(&null_base),
            vec![FsymTrustIrDiagnosticKind::NullDeref]
        );

        // In bounds of a tracked object: clean.
        let in_bounds = scan_body(
            "fsym_gep_clean",
            vec![
                const_u64(9, 4),
                u8_alloca(0, Some(9), None),
                const_i64(1, 3),
                i64_gep(2, Ty::U8, 0, 1),
                const_u8(3, 1),
                store_u8(2, 3),
            ],
        );
        assert!(in_bounds.diagnostics.is_empty());
        assert!(in_bounds.unknown_obligations.is_empty(), "{in_bounds:?}");
    }

    #[test]
    fn wasm32_constant_pointer_past_the_address_space_has_no_address() {
        // Measured: at wasm32, the constant pointer 0x1_0000_0000 was a
        // 64-bit non-null address, so a store through it passed null.
        let report = scan_pinned(
            "fsym_wasm32_const_ptr",
            Some(target_info("wasm32-unknown-unknown", 4)),
            vec![
                node(
                    0,
                    Inst::Const {
                        ty: Ty::Ptr,
                        value: Constant::Int(0x1_0000_0000),
                    },
                ),
                const_u8(1, 1),
                store_u8(0, 1),
            ],
        );
        assert!(
            report.unknown_obligations.iter().any(|unknown| unknown.kind
                == FsymTrustIrDiagnosticKind::NullDeref
                && unknown.reason.contains("address is not modeled")),
            "{:?}",
            report.unknown_obligations
        );
    }

    #[test]
    fn shift_amount_is_an_obligation_and_never_folded() {
        // Measured: `shl u64 1, 64` scanned clean and folded to 0.
        let out_of_range = scan_body(
            "fsym_shl_64",
            vec![
                const_u64(0, 1),
                const_u64(1, 64),
                u64_bin(2, BinOp::Shl, 0, 1),
            ],
        );
        assert_eq!(
            diagnostic_kinds(&out_of_range),
            vec![FsymTrustIrDiagnosticKind::Arithmetic]
        );

        // The folded value used to prune: `(1 << 64) != 0` was FALSE.
        let pruned = branch_on(
            vec![
                const_u64(0, 1),
                const_u64(1, 64),
                u64_bin(2, BinOp::Shl, 0, 1),
                const_u64(4, 0),
                node(
                    3,
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::U64,
                        lhs: v(2),
                        rhs: v(4),
                    },
                ),
            ],
            3,
        );
        assert!(
            pruned
                .unknown_obligations
                .iter()
                .any(|unknown| unknown.block == 2),
            "the arm a masking target runs must be walked: {pruned:?}"
        );

        // An unmodeled value shifted by a constant in range owes nothing.
        let in_range = scan_body(
            "fsym_shl_loaded",
            vec![
                alloca_i64(0),
                init_slot(0, 8)[0].clone(),
                init_slot(0, 8)[1].clone(),
                load(1, Ty::U64, 0, None),
                const_u64(2, 63),
                u64_bin(3, BinOp::LShr, 1, 2),
            ],
        );
        assert!(in_range.diagnostics.is_empty());
        assert!(in_range.unknown_obligations.is_empty(), "{in_range:?}");

        // A symbolic amount escalates as a typed ShiftAmount candidate.
        let symbolic = scan_with_params(
            "fsym_shl_param",
            vec![(v(10), Ty::U64)],
            vec![const_u64(0, 1), u64_bin(2, BinOp::Shl, 0, 10)],
        );
        assert!(matches!(
            symbolic.unknown_obligations[..],
            [super::FsymTrustIrUnknown {
                kind: FsymTrustIrDiagnosticKind::Arithmetic,
                solver_candidate: Some(super::FsymTrustIrSolverCandidate {
                    obligation: FsymTrustIrSolverObligation::Arithmetic {
                        kind: ArithUbKind::ShiftAmount,
                        width: 64,
                        ..
                    },
                    ..
                }),
                ..
            }]
        ));
    }

    #[test]
    fn dealloc_is_a_checked_site() {
        let kinds_of = |name: &str, params: Vec<(ValueId, Ty)>, body: Vec<InstrNode>| {
            let report = scan_with_params(name, params, body);
            assert!(report.coverage_errors.is_empty(), "{name}");
            (diagnostic_kinds(&report), unknown_kinds(&report))
        };
        // Measured: all four scanned clean.
        let (diag, _) = kinds_of(
            "fsym_double_free_heap",
            vec![],
            vec![
                heap_i64(0),
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
            ],
        );
        assert_eq!(diag, vec![FsymTrustIrDiagnosticKind::UseAfterFree]);
        let (diag, unknown) = kinds_of(
            "fsym_double_free_param",
            vec![(v(0), Ty::Ptr)],
            vec![
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
            ],
        );
        assert!(diag.is_empty());
        assert!(unknown.contains(&FsymTrustIrDiagnosticKind::InvalidFree));
        assert!(unknown.contains(&FsymTrustIrDiagnosticKind::UseAfterFree));
        let (diag, _) = kinds_of(
            "fsym_free_stack",
            vec![],
            vec![alloca_i64(0), InstrNode::new(Inst::Dealloc { ptr: v(0) })],
        );
        assert_eq!(diag, vec![FsymTrustIrDiagnosticKind::InvalidFree]);
        let (diag, _) = kinds_of(
            "fsym_free_interior",
            vec![],
            vec![
                const_u64(9, 8),
                node(
                    0,
                    Inst::HeapAlloc {
                        ty: Ty::U8,
                        count: Some(v(9)),
                        align: None,
                        origin: trust_ir::inst::AllocOrigin::CMalloc,
                    },
                ),
                const_i64(1, 1),
                i64_gep(2, Ty::U8, 0, 1),
                InstrNode::new(Inst::Dealloc { ptr: v(2) }),
            ],
        );
        assert_eq!(diag, vec![FsymTrustIrDiagnosticKind::InvalidFree]);
        let (diag, _) = kinds_of(
            "fsym_free_null",
            vec![],
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
            ],
        );
        assert_eq!(diag, vec![FsymTrustIrDiagnosticKind::InvalidFree]);
        // A reference-counted cell is released by `Release`, never by
        // `Dealloc`: freeing it at its base is an invalid free, as trust-ir's
        // reference interpreter (`MemoryState::dealloc`) and Lean's
        // `semDealloc` both rule. Before trust-ir `bf7ee706` both origins
        // scanned clean here. Every origin, against trust-ir's proved table
        // `AllocOrigin::is_reference_counted` (the interpreter's `Dealloc`
        // reads the same one): an invalid free exactly on its true cells.
        for origin in [
            trust_ir::inst::AllocOrigin::RustHeap,
            trust_ir::inst::AllocOrigin::SwiftHeap,
            trust_ir::inst::AllocOrigin::CMalloc,
            trust_ir::inst::AllocOrigin::CleanHeap,
        ] {
            let (diag, unknown) = kinds_of(
                "fsym_free_heap_cell",
                vec![],
                vec![
                    node(
                        0,
                        Inst::HeapAlloc {
                            ty: Ty::I64,
                            count: None,
                            align: None,
                            origin,
                        },
                    ),
                    InstrNode::new(Inst::Dealloc { ptr: v(0) }),
                ],
            );
            if origin.is_reference_counted() {
                assert_eq!(
                    diag,
                    vec![FsymTrustIrDiagnosticKind::InvalidFree],
                    "{origin:?}"
                );
            } else {
                assert!(
                    diag.is_empty() && unknown.is_empty(),
                    "{origin:?}: {diag:?} {unknown:?}"
                );
            }
        }
        // A valid free of a heap base is clean, for both non-RC origins.
        let (diag, unknown) = kinds_of(
            "fsym_free_rust_heap_ok",
            vec![],
            vec![
                node(
                    0,
                    Inst::HeapAlloc {
                        ty: Ty::I64,
                        count: None,
                        align: None,
                        origin: trust_ir::inst::AllocOrigin::RustHeap,
                    },
                ),
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
            ],
        );
        assert!(
            diag.is_empty() && unknown.is_empty(),
            "{diag:?} {unknown:?}"
        );
        let (diag, unknown) = kinds_of(
            "fsym_free_ok",
            vec![],
            vec![heap_i64(0), InstrNode::new(Inst::Dealloc { ptr: v(0) })],
        );
        assert!(
            diag.is_empty() && unknown.is_empty(),
            "{diag:?} {unknown:?}"
        );
    }

    #[test]
    fn call_argument_type_decides_pointer_carrying_too() {
        // Measured: `bzero` declared `(u64, u64)` and passed a NullPtr was
        // judged on the declaration alone: an integer, so accounted.
        let report = scan_call(
            "bzero",
            vec![Ty::U64, Ty::U64],
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                const_u64(1, 8),
            ],
            &[0, 1],
        );
        assert_eq!(
            unknown_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::UnsummarizedCall]
        );
        assert!(report.unknown_obligations[0].reason.contains("#0 (Ptr)"));
    }

    #[test]
    fn a_call_havocs_the_objects_it_can_reach() {
        // `g` (bodied, in scope) may free or overwrite `a`; the caller's
        // later load of `a` is no longer provable.
        let mut module = test_module(
            "fsym_call_havoc",
            vec![
                alloca_i64(0),
                init_slot(0, 8)[0].clone(),
                init_slot(0, 8)[1].clone(),
                call(FuncId::new(1), &[0]),
                load(1, Ty::I64, 0, None),
                ret_i64(1),
            ],
        );
        let ty = FuncTyId::new(module.func_types.len() as u32);
        module.func_types.push(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        });
        let mut callee = Function::new(FuncId::new(1), "g", ty, BlockId::new(0));
        callee.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![InstrNode::new(Inst::Return { values: vec![] })],
        }];
        module.functions.push(callee);
        let report = scan_module(&module);
        let caller = report
            .unknown_obligations
            .iter()
            .filter(|unknown| unknown.function == "test")
            .map(|unknown| unknown.kind)
            .collect::<Vec<_>>();
        assert_eq!(
            caller,
            vec![
                FsymTrustIrDiagnosticKind::UseAfterFree,
                FsymTrustIrDiagnosticKind::Uninitialized
            ]
        );
    }

    #[test]
    fn a_free_that_may_be_under_a_live_borrow_is_never_proven() {
        // trust-ir c06a487f: `Dealloc` of an allocation under a live
        // `Borrow` / `BorrowMut` (not yet ended by `EndBorrow`) is UB in the
        // reference interpreter. fsym tracks no borrow counts, so its
        // InvalidFree verdict must not be Safe where one may be live.
        let invalid_free_unknown = |report: &super::FsymTrustIrReport| {
            report.unknown_obligations.iter().any(|unknown| {
                unknown.function == "test" && unknown.kind == FsymTrustIrDiagnosticKind::InvalidFree
            })
        };
        let borrow = |result: u32, ptr: u32| node(result, Inst::Borrow { ptr: v(ptr) });
        // Control: a heap base freed with no borrow and no call is clean.
        let report = scan_body(
            "fsym_free_heap_unborrowed",
            vec![heap_i64(0), InstrNode::new(Inst::Dealloc { ptr: v(0) })],
        );
        assert!(clean(&report), "{report:?}");
        // Borrowed on this path, the borrow live at the free.
        let report = scan_body(
            "fsym_free_heap_borrowed",
            vec![
                heap_i64(0),
                borrow(1, 0),
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
            ],
        );
        assert!(report.diagnostics.is_empty(), "{report:?}");
        assert!(invalid_free_unknown(&report), "{report:?}");
        // A callee borrows the object it is handed and returns without
        // ending the borrow: the caller's free is UB in the interpreter.
        // Before this rule fsym proved the caller's InvalidFree Safe here.
        let mut module = test_module(
            "fsym_free_after_a_borrowing_call",
            vec![
                heap_i64(0),
                call(FuncId::new(1), &[0]),
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
                const_i64(1, 0),
                ret_i64(1),
            ],
        );
        let ty = FuncTyId::new(module.func_types.len() as u32);
        module.func_types.push(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        });
        let mut callee = Function::new(FuncId::new(1), "g", ty, BlockId::new(0));
        callee.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                borrow(1, 0),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }];
        module.functions.push(callee);
        let report = scan_module(&module);
        assert!(invalid_free_unknown(&report), "{report:?}");
        assert!(
            report
                .unknown_obligations
                .iter()
                .any(|unknown| unknown.function == "test"
                    && unknown.kind == FsymTrustIrDiagnosticKind::InvalidFree
                    && unknown.reason.contains("may have left a borrow of it live")),
            "{:?}",
            report.unknown_obligations
        );
    }

    #[test]
    fn an_object_reached_through_an_untracked_value_is_havocked_too() {
        // `select c, a, a` carries no pointer facts, so handing it to `g`
        // must still count as handing `a`.
        let mut module = test_module(
            "fsym_call_havoc_select",
            vec![
                alloca_i64(0),
                init_slot(0, 8)[0].clone(),
                init_slot(0, 8)[1].clone(),
                const_bool(1, true),
                node(
                    2,
                    Inst::Select {
                        ty: Ty::Ptr,
                        cond: v(1),
                        then_val: v(0),
                        else_val: v(0),
                    },
                ),
                call(FuncId::new(1), &[2]),
                load(3, Ty::I64, 0, None),
                ret_i64(3),
            ],
        );
        let ty = FuncTyId::new(module.func_types.len() as u32);
        module.func_types.push(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        });
        let mut callee = Function::new(FuncId::new(1), "g", ty, BlockId::new(0));
        callee.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![InstrNode::new(Inst::Return { values: vec![] })],
        }];
        module.functions.push(callee);
        let report = scan_module(&module);
        assert!(
            report
                .unknown_obligations
                .iter()
                .any(|unknown| unknown.function == "test"
                    && unknown.kind == FsymTrustIrDiagnosticKind::UseAfterFree),
            "{:?}",
            report.unknown_obligations
        );
    }

    #[test]
    fn an_object_reached_through_a_transmuted_pointer_is_havocked_too() {
        // `transmute::<*mut i64, *mut i64>(a)` keeps `a`'s address and
        // provenance (the reference interpreter returns the operand verbatim)
        // but carries no pointer facts here, so handing it to `g` must still
        // count as handing `a`.
        let mut module = test_module(
            "fsym_call_havoc_transmute",
            vec![
                alloca_i64(0),
                init_slot(0, 8)[0].clone(),
                init_slot(0, 8)[1].clone(),
                node(
                    2,
                    Inst::Cast {
                        op: trust_ir::CastOp::Transmute,
                        src_ty: Ty::Ptr,
                        dst_ty: Ty::Ptr,
                        operand: v(0),
                    },
                ),
                call(FuncId::new(1), &[2]),
                load(3, Ty::I64, 0, None),
                ret_i64(3),
            ],
        );
        let ty = FuncTyId::new(module.func_types.len() as u32);
        module.func_types.push(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        });
        let mut callee = Function::new(FuncId::new(1), "g", ty, BlockId::new(0));
        callee.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![InstrNode::new(Inst::Return { values: vec![] })],
        }];
        module.functions.push(callee);
        let report = scan_module(&module);
        assert!(
            report
                .unknown_obligations
                .iter()
                .any(|unknown| unknown.function == "test"
                    && unknown.kind == FsymTrustIrDiagnosticKind::UseAfterFree),
            "{:?}",
            report.unknown_obligations
        );
    }

    #[test]
    fn caller_of_a_refused_callee_is_unsummarized() {
        // Measured: the per-function summary showed a caller CLEAN when the
        // callee it hands an alloca to was refused (CallIndirect).
        let mut module = test_module(
            "fsym_refused_callee",
            vec![
                alloca_i64(0),
                call(FuncId::new(1), &[0]),
                const_i64(1, 0),
                ret_i64(1),
            ],
        );
        let ty = FuncTyId::new(module.func_types.len() as u32);
        module.func_types.push(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        });
        let mut callee = Function::new(FuncId::new(1), "g", ty, BlockId::new(0));
        callee.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::CallIndirect {
                    callee: v(0),
                    sig: ty,
                    args: vec![],
                    calling_conv: trust_ir::CallingConv::default(),
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }];
        module.functions.push(callee);
        let report = super::scan_function_in_module(&module, &module.functions[0]);
        assert_eq!(
            unknown_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::UnsummarizedCall]
        );
        assert!(
            report.unknown_obligations[0]
                .reason
                .contains("fsym does not scan it"),
            "{:?}",
            report.unknown_obligations
        );
    }

    #[test]
    fn unreachable_is_a_checked_site() {
        // Reached at entry: UB.
        let entry = scan_module(&test_module(
            "fsym_unreachable_entry",
            vec![InstrNode::new(Inst::Unreachable)],
        ));
        assert_eq!(
            diagnostic_kinds(&entry),
            vec![FsymTrustIrDiagnosticKind::UnreachableReached]
        );
        // After a call that may not return: Unknown.
        let mut module = test_module(
            "fsym_unreachable_after_call",
            vec![call(FuncId::new(1), &[]), InstrNode::new(Inst::Unreachable)],
        );
        declare(&mut module, "abort", vec![]);
        let after_call = scan_module(&module);
        assert!(after_call.diagnostics.is_empty());
        assert_eq!(
            unknown_kinds(&after_call)
                .into_iter()
                .filter(|kind| *kind == FsymTrustIrDiagnosticKind::UnreachableReached)
                .count(),
            1
        );
        // Behind a symbolic guard: Unknown with a reachability candidate.
        let guarded = scan_module(&test_module_blocks(
            "fsym_unreachable_guarded",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![(v(0), Ty::I64)],
                    body: vec![
                        const_i64(1, 3),
                        icmp_i64(2, ICmpOp::Eq, 0, 1),
                        condbr(2, 1, &[], 2, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Unreachable)],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![const_i64(3, 0), ret_i64(3)],
                },
            ],
        ));
        assert!(matches!(
            guarded.unknown_obligations[..],
            [super::FsymTrustIrUnknown {
                kind: FsymTrustIrDiagnosticKind::UnreachableReached,
                solver_candidate: Some(super::FsymTrustIrSolverCandidate {
                    obligation: FsymTrustIrSolverObligation::Reachable,
                    ..
                }),
                ..
            }]
        ));
    }

    #[test]
    fn alignment_is_checked_against_the_object_base() {
        // Measured: `load i64 align 8` at byte 1 of a 16-byte `align 8`
        // buffer scanned clean.
        let misaligned = scan_body(
            "fsym_misaligned",
            vec![
                const_u64(9, 16),
                u8_alloca(0, Some(9), Some(8)),
                const_u8(8, 0),
                memset(0, 8, 9),
                const_i64(1, 1),
                i64_gep(2, Ty::U8, 0, 1),
                load(3, Ty::I64, 2, Some(8)),
            ],
        );
        assert_eq!(
            diagnostic_kinds(&misaligned),
            vec![FsymTrustIrDiagnosticKind::Misaligned]
        );
        // The base is only guaranteed 1-byte alignment: not decidable.
        let weak_base = scan_body(
            "fsym_weak_base",
            vec![
                const_u64(9, 16),
                u8_alloca(0, Some(9), None),
                const_u8(8, 0),
                memset(0, 8, 9),
                const_i64(1, 8),
                i64_gep(2, Ty::U8, 0, 1),
                load(3, Ty::I64, 2, None),
            ],
        );
        assert!(weak_base.diagnostics.is_empty());
        assert_eq!(
            unknown_kinds(&weak_base),
            vec![FsymTrustIrDiagnosticKind::Misaligned]
        );
        // Aligned: clean.
        let aligned = scan_body(
            "fsym_aligned",
            vec![
                const_u64(9, 16),
                u8_alloca(0, Some(9), Some(8)),
                const_u8(8, 0),
                memset(0, 8, 9),
                const_i64(1, 8),
                i64_gep(2, Ty::U8, 0, 1),
                load(3, Ty::I64, 2, Some(8)),
            ],
        );
        assert!(aligned.diagnostics.is_empty());
        assert!(aligned.unknown_obligations.is_empty(), "{aligned:?}");
    }

    #[test]
    fn reads_of_bytes_not_written_are_unknown() {
        let fresh = scan_body(
            "fsym_uninit_load",
            vec![alloca_i64(0), load(1, Ty::I64, 0, None)],
        );
        assert_eq!(
            unknown_kinds(&fresh),
            vec![FsymTrustIrDiagnosticKind::Uninitialized]
        );
        let written = scan_body(
            "fsym_init_load",
            vec![
                alloca_i64(0),
                init_slot(0, 8)[0].clone(),
                init_slot(0, 8)[1].clone(),
                load(1, Ty::I64, 0, None),
            ],
        );
        assert!(written.unknown_obligations.is_empty(), "{written:?}");
        // A copy moves poison: an initialized destination overwritten from an
        // unwritten source reads as uninitialized again.
        let copied = scan_body(
            "fsym_copy_poison",
            vec![
                alloca_i64(0),
                init_slot(0, 8)[0].clone(),
                init_slot(0, 8)[1].clone(),
                alloca_i64(1),
                memcopy(0, 1, 8, false),
                load(2, Ty::I64, 0, None),
            ],
        );
        assert_eq!(
            unknown_kinds(&copied),
            vec![FsymTrustIrDiagnosticKind::Uninitialized]
        );
    }

    #[test]
    fn allocation_count_must_be_positive() {
        let zero = scan_body(
            "fsym_alloca_zero",
            vec![const_u64(9, 0), u8_alloca(0, Some(9), None)],
        );
        assert_eq!(
            diagnostic_kinds(&zero),
            vec![FsymTrustIrDiagnosticKind::Arithmetic]
        );
        let symbolic = scan_with_params(
            "fsym_alloca_param",
            vec![(v(9), Ty::U64)],
            vec![u8_alloca(0, Some(9), None)],
        );
        assert_eq!(
            unknown_kinds(&symbolic),
            vec![FsymTrustIrDiagnosticKind::Arithmetic]
        );
    }

    #[test]
    fn an_inbounds_annotation_on_a_gep_is_not_an_access_proof() {
        // The LLVM importer turns `getelementptr inbounds` into an InBounds
        // proof on the GEP. Past the object it yields poison, not an
        // in-bounds pointer: the access is still checked.
        let report = scan_body(
            "fsym_inbounds_gep",
            vec![
                const_u64(9, 4),
                u8_alloca(0, Some(9), None),
                const_i64(1, 100),
                i64_gep(2, Ty::U8, 0, 1).with_proof(trust_ir::ProofAnnotation::InBounds),
                const_u8(3, 1),
                store_u8(2, 3),
            ],
        );
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
    }

    #[test]
    fn path_state_bound_names_the_function_unknown() {
        // Measured: a chain of 6 Switch blocks took 6.46 s (debug) and 16
        // blocks allow 15 levels.
        let levels = super::FSYM_TRUST_IR_MAX_BLOCKS as u32 - 1;
        let cases = (1..=super::FSYM_TRUST_IR_MAX_SWITCH_CASES as i128).collect::<Vec<_>>();
        let mut blocks = Vec::new();
        for level in 0..levels {
            let next = BlockId::new(level + 1);
            blocks.push(Block {
                id: BlockId::new(level),
                params: if level == 0 {
                    vec![(v(0), Ty::U8)]
                } else {
                    vec![]
                },
                body: vec![InstrNode::new(Inst::Switch {
                    value: v(0),
                    default: next,
                    default_args: vec![],
                    cases: cases
                        .iter()
                        .map(|case| SwitchCase {
                            value: Constant::Int(*case),
                            target: next,
                            args: vec![],
                        })
                        .collect(),
                    exhaustive_enum_unreachable: false,
                })],
            });
        }
        blocks.push(Block {
            id: BlockId::new(levels),
            params: vec![],
            body: vec![const_i64(1, 0), ret_i64(1)],
        });
        let started = std::time::Instant::now();
        let report = scan_module(&test_module_blocks("fsym_switch_chain", blocks));
        assert!(started.elapsed() < std::time::Duration::from_secs(20));
        assert!(
            unknown_kinds(&report).contains(&FsymTrustIrDiagnosticKind::ScanBound),
            "{:?}",
            report.unknown_obligations
        );
    }

    #[test]
    fn every_checked_kind_is_stated_as_a_ub_class() {
        let report = super::FsymTrustIrReport::default();
        let checked = report
            .ub_classes()
            .iter()
            .filter_map(|class| match class.status {
                super::FsymUbClassStatus::Checked(kind) => Some(kind),
                super::FsymUbClassStatus::NotChecked => None,
            })
            .collect::<Vec<_>>();
        for kind in [
            FsymTrustIrDiagnosticKind::NullDeref,
            FsymTrustIrDiagnosticKind::Arithmetic,
            FsymTrustIrDiagnosticKind::OutOfBounds,
            FsymTrustIrDiagnosticKind::UseAfterFree,
            FsymTrustIrDiagnosticKind::Overlap,
            FsymTrustIrDiagnosticKind::UnsummarizedCall,
            FsymTrustIrDiagnosticKind::InvalidFree,
            FsymTrustIrDiagnosticKind::PointerArithmetic,
            FsymTrustIrDiagnosticKind::Misaligned,
            FsymTrustIrDiagnosticKind::Uninitialized,
            FsymTrustIrDiagnosticKind::UnreachableReached,
        ] {
            assert!(checked.contains(&kind), "{kind:?} is not stated");
        }
        assert_eq!(
            report.render_ub_classes().len(),
            super::FSYM_TRUST_IR_UB_CLASSES.len()
        );
    }

    // -----------------------------------------------------------------------
    // Round 4: float-to-int, element indices, enum lanes, borrows, Bool
    // widening, annotations against exact facts, address-holding stores.
    // -----------------------------------------------------------------------

    fn unknown_count(report: &super::FsymTrustIrReport) -> usize {
        report.unknown_obligations.len()
    }

    fn clean(report: &super::FsymTrustIrReport) -> bool {
        report.scanned_functions == 1
            && report.skipped_functions.is_empty()
            && report.diagnostics.is_empty()
            && report.unknown_obligations.is_empty()
            && report.coverage_errors.is_empty()
    }

    fn value(result: u32, inst: Inst) -> InstrNode {
        InstrNode::new(inst).with_result(v(result))
    }

    fn float(result: u32, ty: Ty, x: f64) -> InstrNode {
        value(
            result,
            Inst::Const {
                ty,
                value: Constant::Float(x),
            },
        )
    }

    #[test]
    fn zext_and_sext_of_a_bool_are_modeled_not_a_panic() {
        // `8 / ((1 < 0) as u64)`: zext of a Bool-sorted comparison asked the
        // Bool for a bit width (BoolHasNoWidth).
        let report = scan_body(
            "fsym_zext_bool",
            vec![
                const_u64(0, 1),
                const_u64(1, 0),
                value(
                    2,
                    Inst::ICmp {
                        op: ICmpOp::Ult,
                        ty: Ty::U64,
                        lhs: v(0),
                        rhs: v(1),
                    },
                ),
                cast(3, trust_ir::CastOp::ZExt, Ty::Bool, Ty::U64, 2),
                const_u64(4, 8),
                value(
                    5,
                    Inst::BinOp {
                        op: BinOp::UDiv,
                        ty: Ty::U64,
                        lhs: v(4),
                        rhs: v(3),
                    },
                ),
            ],
        );
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::Arithmetic]
        );
        // sext(true) is all ones: `8 / (sext(0 < 1) + 1)` divides by zero.
        let report = scan_body(
            "fsym_sext_bool",
            vec![
                const_i64(0, 0),
                const_i64(1, 1),
                icmp_i64(2, ICmpOp::Slt, 0, 1),
                cast(3, trust_ir::CastOp::SExt, Ty::Bool, Ty::I64, 2),
                bin_i64(4, BinOp::Add, 3, 1),
                const_i64(5, 8),
                bin_i64(6, BinOp::SDiv, 5, 4),
            ],
        );
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::Arithmetic]
        );
    }

    #[test]
    fn a_select_of_bools_is_a_branch_condition_not_a_panic() {
        // `select c, (a < b), (b < a)` was an `ite` over Bools, whose sort
        // asked a Bool for a bit width.
        let report = scan_module(&test_module_blocks(
            "fsym_select_bools",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        const_i64(0, 1),
                        const_i64(1, 2),
                        icmp_i64(2, ICmpOp::Slt, 0, 1),
                        icmp_i64(3, ICmpOp::Slt, 1, 0),
                        value(
                            4,
                            Inst::Select {
                                ty: Ty::Bool,
                                cond: v(2),
                                then_val: v(3),
                                else_val: v(2),
                            },
                        ),
                        condbr(4, 1, &[], 2, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![const_i64(5, 0), ret_i64(5)],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![const_i64(6, 0), ret_i64(6)],
                },
            ],
        ));
        assert!(clean(&report), "{report:?}");
    }

    #[test]
    fn raw_float_to_int_casts_owe_a_range_verdict() {
        for (x, op, dst, ub) in [
            (f64::NAN, trust_ir::CastOp::FPToSI, Ty::I32, true),
            (-0.5, trust_ir::CastOp::FPToUI, Ty::U8, true),
            (255.9, trust_ir::CastOp::FPToUI, Ty::U8, false),
            (256.0, trust_ir::CastOp::FPToUI, Ty::U8, true),
            (-2_147_483_648.0, trust_ir::CastOp::FPToSI, Ty::I32, false),
            (2_147_483_648.0, trust_ir::CastOp::FPToSI, Ty::I32, true),
            (f64::NEG_INFINITY, trust_ir::CastOp::FPToSI, Ty::I64, true),
        ] {
            let report = scan_body(
                "fsym_fptoint",
                vec![float(0, Ty::F64, x), cast(1, op, Ty::F64, dst.clone(), 0)],
            );
            if ub {
                assert_eq!(
                    diagnostic_kinds(&report),
                    vec![FsymTrustIrDiagnosticKind::Arithmetic],
                    "{x} {op} {dst:?}"
                );
            } else {
                assert!(clean(&report), "{x} {op} {dst:?}: {report:?}");
            }
        }
        // An f32 constant is rounded before it is converted: 2147483647 as
        // f32 is 2^31, one past i32::MAX.
        let report = scan_body(
            "fsym_fptoint_f32",
            vec![
                float(0, Ty::F32, 2_147_483_647.0),
                cast(1, trust_ir::CastOp::FPToSI, Ty::F32, Ty::I32, 0),
            ],
        );
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::Arithmetic]
        );
        // An unmodeled float (a parameter, arithmetic) is an Unknown; the
        // saturating casts owe nothing.
        let report = scan_with_params(
            "fsym_fptoint_param",
            vec![(v(0), Ty::F64)],
            vec![
                cast(1, trust_ir::CastOp::FPToSI, Ty::F64, Ty::I64, 0),
                cast(2, trust_ir::CastOp::FPToSISat, Ty::F64, Ty::I64, 0),
            ],
        );
        assert!(report.diagnostics.is_empty());
        assert_eq!(
            unknown_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::Arithmetic]
        );
    }

    #[test]
    fn element_indices_are_checked_against_the_lane_count() {
        let vector = |result: u32| {
            value(
                result,
                Inst::Const {
                    ty: Ty::Vector(Box::new(Ty::I32), 4),
                    value: Constant::Vector((0..4).map(Constant::Int).collect()),
                },
            )
        };
        let extract = |index: u32| {
            value(
                2,
                Inst::ExtractElement {
                    ty: Ty::I32,
                    array: v(0),
                    index: v(index),
                },
            )
        };
        let report = scan_body("fsym_elem_in", vec![vector(0), const_u64(1, 3), extract(1)]);
        assert!(clean(&report), "{report:?}");
        let report = scan_body(
            "fsym_elem_past",
            vec![vector(0), const_u64(1, 4), extract(1)],
        );
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
        let report = scan_body(
            "fsym_elem_neg",
            vec![vector(0), const_i64(1, -1), extract(1)],
        );
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
        let report = scan_with_params(
            "fsym_elem_param",
            vec![(v(1), Ty::U64)],
            vec![vector(0), extract(1)],
        );
        assert!(report.diagnostics.is_empty());
        assert_eq!(
            unknown_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
    }

    fn enum_module(name: &str, params: Vec<(ValueId, Ty)>, mut body: Vec<InstrNode>) -> Module {
        body.push(const_i64(99, 0));
        body.push(ret_i64(99));
        let mut module = test_module_blocks(
            name,
            vec![Block {
                id: BlockId::new(0),
                params,
                body,
            }],
        );
        module.enums.push(trust_ir::EnumDef::new(
            trust_ir::EnumId::new(0),
            "E",
            vec![
                trust_ir::EnumVariant {
                    name: "A".to_string(),
                    fields: vec![],
                    field_names: vec![],
                },
                trust_ir::EnumVariant {
                    name: "B".to_string(),
                    fields: vec![Ty::I32],
                    field_names: vec![],
                },
                trust_ir::EnumVariant {
                    name: "C".to_string(),
                    fields: vec![Ty::I32, Ty::U8],
                    field_names: vec![],
                },
            ],
        ));
        module
    }

    #[test]
    fn enum_byte_images_are_refused_before_scanning() {
        let mut module = enum_module("fsym_enum_image_gate", vec![], vec![]);
        let enum_ty = Ty::Enum(trust_ir::EnumId::new(0));
        module.types.push(enum_ty.clone());

        assert!(super::type_may_contain_enum_by_value(&module, &enum_ty));
        assert!(super::type_may_contain_enum_by_value(
            &module,
            &Ty::Tuple(vec![Ty::U8, enum_ty.clone()])
        ));
        assert!(super::type_may_contain_enum_by_value(
            &module,
            &Ty::Array(trust_ir::TyId::new(0), 1)
        ));
        assert!(!super::type_may_contain_enum_by_value(
            &module,
            &Ty::PtrConst(Box::new(enum_ty.clone()))
        ));

        let load = Inst::Load {
            ty: enum_ty.clone(),
            ptr: v(0),
            volatile: false,
            align: None,
        };
        let cast_from = Inst::Cast {
            op: trust_ir::CastOp::Bitcast,
            src_ty: enum_ty.clone(),
            dst_ty: Ty::Unit,
            operand: v(0),
        };
        let cast_to = Inst::Cast {
            op: trust_ir::CastOp::Bitcast,
            src_ty: Ty::Unit,
            dst_ty: enum_ty,
            operand: v(0),
        };
        for inst in [&load, &cast_from, &cast_to] {
            let detail = super::unsupported_nonterminator_detail(&module, inst)
                .expect("enum-containing byte-image operation is refused");
            assert!(detail.contains("enum-containing"), "{detail}");
        }
        assert_eq!(
            super::unsupported_nonterminator_detail(
                &module,
                &Inst::Load {
                    ty: Ty::U8,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                }
            ),
            None
        );
    }

    #[test]
    fn enum_lanes_must_belong_to_the_active_variant() {
        let e = Ty::Enum(trust_ir::EnumId::new(0));
        let variant_const = |result: u32, elems: Vec<i128>| {
            value(
                result,
                Inst::Const {
                    ty: Ty::Enum(trust_ir::EnumId::new(0)),
                    value: Constant::Aggregate(elems.into_iter().map(Constant::Int).collect()),
                },
            )
        };
        let extract = |result: u32, ty: Ty, field: u32| {
            value(
                result,
                Inst::ExtractField {
                    ty,
                    aggregate: v(0),
                    field,
                },
            )
        };
        // B's payload read from B: safe; from A: UB.
        let module = enum_module(
            "fsym_enum_b",
            vec![],
            vec![variant_const(0, vec![1, 5]), extract(1, Ty::I32, 1)],
        );
        assert!(clean(&scan_module(&module)));
        let module = enum_module(
            "fsym_enum_a",
            vec![],
            vec![variant_const(0, vec![0]), extract(1, Ty::I32, 1)],
        );
        assert_eq!(
            diagnostic_kinds(&scan_module(&module)),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
        // A parameter's variant is unknown: lane 1 as I32 belongs to B and C
        // only (Unknown); lane 2 as I64 to none (UB whenever reached).
        let module = enum_module(
            "fsym_enum_param",
            vec![(v(0), e.clone())],
            vec![extract(1, Ty::I32, 1)],
        );
        assert_eq!(
            unknown_kinds(&scan_module(&module)),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
        let module = enum_module(
            "fsym_enum_param_no_lane",
            vec![(v(0), e.clone())],
            vec![extract(1, Ty::I64, 2)],
        );
        assert_eq!(
            diagnostic_kinds(&scan_module(&module)),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
        // The tag is always readable, never rewritable; a lane write keeps
        // the variant.
        let module = enum_module(
            "fsym_enum_tag",
            vec![(v(0), e.clone())],
            vec![
                extract(1, Ty::U8, 0),
                value(
                    2,
                    Inst::InsertField {
                        ty: e.clone(),
                        aggregate: v(0),
                        field: 0,
                        value: v(1),
                    },
                ),
            ],
        );
        let report = scan_module(&module);
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
        assert_eq!(report.diagnostics[0].inst_index, 1);
        let module = enum_module(
            "fsym_enum_insert_keeps_variant",
            vec![],
            vec![
                variant_const(0, vec![2, 1, 2]),
                const_i64(1, 0),
                value(
                    2,
                    Inst::Cast {
                        op: trust_ir::CastOp::Trunc,
                        src_ty: Ty::I64,
                        dst_ty: Ty::I32,
                        operand: v(1),
                    },
                ),
                value(
                    3,
                    Inst::InsertField {
                        ty: e,
                        aggregate: v(0),
                        field: 1,
                        value: v(2),
                    },
                ),
                value(
                    4,
                    Inst::ExtractField {
                        ty: Ty::U8,
                        aggregate: v(3),
                        field: 2,
                    },
                ),
            ],
        );
        assert!(clean(&scan_module(&module)));
    }

    #[test]
    fn a_borrow_needs_a_non_null_pointer_with_provenance() {
        let borrow = |ptr: u32| value(1, Inst::Borrow { ptr: v(ptr) });
        let report = scan_body(
            "fsym_borrow_null",
            vec![InstrNode::new(Inst::NullPtr).with_result(v(0)), borrow(0)],
        );
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::NullDeref]
        );
        let report = scan_body("fsym_borrow_alloca", vec![alloca_i64(0), borrow(0)]);
        assert!(clean(&report), "{report:?}");
        let report = scan_with_params("fsym_borrow_param", vec![(v(0), Ty::Ptr)], vec![borrow(0)]);
        assert!(report.diagnostics.is_empty());
        assert!(
            unknown_kinds(&report).contains(&FsymTrustIrDiagnosticKind::OutOfBounds),
            "{report:?}"
        );
    }

    #[test]
    fn annotations_never_override_an_exact_address_or_offset() {
        // NotNull on a load through a literal null.
        let report = scan_body(
            "fsym_notnull_on_null",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                })
                .with_result(v(1))
                .with_proof(trust_ir::ProofAnnotation::NotNull),
            ],
        );
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::NullDeref]
        );
        // InBounds on a store through a constant address naming no
        // allocation the scanner knows.
        let report = scan_body(
            "fsym_inbounds_on_constant",
            vec![
                const_u64(0, 0x1000),
                cast(1, trust_ir::CastOp::IntToPtr, Ty::U64, Ty::Ptr, 0),
                const_u8(2, 1),
                InstrNode::new(Inst::Store {
                    ty: Ty::U8,
                    ptr: v(1),
                    value: v(2),
                    volatile: false,
                    align: None,
                })
                .with_proof(trust_ir::ProofAnnotation::InBounds),
            ],
        );
        let kinds = unknown_kinds(&report);
        assert!(
            kinds.contains(&FsymTrustIrDiagnosticKind::OutOfBounds)
                && kinds.contains(&FsymTrustIrDiagnosticKind::UseAfterFree),
            "{kinds:?}"
        );
        // InBounds on a store at a constant offset past a tracked object.
        let report = scan_body(
            "fsym_inbounds_past_object",
            vec![
                alloca_i64(0),
                const_i64(1, 8),
                byte_gep(2, 0, 1),
                const_u8(3, 1),
                InstrNode::new(Inst::Store {
                    ty: Ty::U8,
                    ptr: v(2),
                    value: v(3),
                    volatile: false,
                    align: None,
                })
                .with_proof(trust_ir::ProofAnnotation::InBounds),
            ],
        );
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
    }

    #[test]
    fn storing_an_aggregate_that_holds_a_pointer_exposes_its_address() {
        let pair = Ty::Tuple(vec![Ty::Ptr, Ty::I64]);
        let ints = Ty::Tuple(vec![Ty::I32, Ty::I64]);
        let module = test_module("fsym_store_pair", vec![]);
        let owed = super::fsym_owed_kinds(
            &module,
            &Inst::Store {
                ty: pair,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            },
        );
        assert!(owed.contains(&FsymTrustIrDiagnosticKind::PointerArithmetic));
        let owed = super::fsym_owed_kinds(
            &module,
            &Inst::Store {
                ty: ints,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            },
        );
        assert!(!owed.contains(&FsymTrustIrDiagnosticKind::PointerArithmetic));
    }

    #[test]
    fn seq_map_is_refused_by_name() {
        assert_skips_unsupported_instruction(
            "fsym_seq_map",
            vec![
                InstrNode::new(Inst::SeqMap {
                    ty: Ty::Sequence(trust_ir::TyId::new(0)),
                    seq: v(0),
                    fwd: FuncId::new(0),
                })
                .with_result(v(1)),
            ],
        );
    }

    #[test]
    fn the_gate_refuses_what_the_interpreter_map_refuses() {
        let module = test_module("fsym_map_gate", vec![]);
        let refusal = crate::fsym_ub_map::fsym_map_refusal(&module, &Inst::IsUnique { ptr: v(0) })
            .expect("IsUnique raises UB fsym refuses");
        assert!(refusal.contains("IsUnique"), "{refusal}");
        assert_eq!(
            crate::fsym_ub_map::fsym_map_refusal(
                &module,
                &Inst::BinOp {
                    op: BinOp::UDiv,
                    ty: Ty::U64,
                    lhs: v(0),
                    rhs: v(1),
                },
            ),
            None
        );
        let _ = unknown_count;
    }

    // ---------------------------------------------------------------------
    // Round 5: the interpreter's layout, natural alignment, globals,
    // padding, target-width solver candidates, annotations.
    // ---------------------------------------------------------------------

    /// `Declared { x: u8 }` declared at offset 8, size 16, align 1 (struct
    /// 0), `Huge` zero-sized, declared align 2^63 (struct 1), and `Pad { a:
    /// u8, b: u64 }` with no declared layout (struct 2).
    fn layout_structs() -> Vec<trust_ir::StructDef> {
        let field = |ty: Ty, offset: Option<u64>| trust_ir::FieldDef {
            name: "f".to_string(),
            ty,
            offset,
        };
        let def = |id: u32, fields, size, align| trust_ir::StructDef {
            origin: None,
            id: trust_ir::StructId::new(id),
            name: format!("S{id}"),
            fields,
            size,
            align,
            repr: trust_ir::StructRepr::Rust,
        };
        vec![
            def(0, vec![field(Ty::U8, Some(8))], Some(16), Some(1)),
            def(1, vec![], Some(0), Some(1 << 63)),
            def(
                2,
                vec![field(Ty::U8, None), field(Ty::U64, None)],
                None,
                None,
            ),
        ]
    }

    fn scan_layout(
        name: &str,
        target: Option<trust_ir::TargetInfo>,
        mut body: Vec<InstrNode>,
    ) -> super::FsymTrustIrReport {
        body.push(const_i64(99, 0));
        body.push(ret_i64(99));
        let mut module = test_module(name, body);
        module.structs = layout_structs();
        module.target_info = target;
        scan_module(&module)
    }

    #[test]
    fn sizes_strides_and_alignments_are_the_interpreters() {
        let mut module = test_module("fsym_layout_authority", vec![]);
        module.structs = layout_structs();
        let layout = crate::fsym_layout::FsymLayout::new(&module);
        let bools = Ty::Vector(Box::new(Ty::Bool), 4);
        let declared = Ty::Struct(trust_ir::StructId::new(0));
        let pad = Ty::Struct(trust_ir::StructId::new(2));
        assert_eq!(layout.size(&bools), Ok(4));
        assert_eq!(layout.align(&bools), Ok(1));
        assert_eq!(layout.size(&declared), Ok(16));
        assert_eq!(layout.align(&declared), Ok(1));
        assert_eq!(layout.size(&pad), Ok(16));
        assert_eq!(layout.align(&pad), Ok(8));
        // A store of `Pad` writes bytes 0 and 8..16; 1..8 are padding.
        let written = layout.written_coverage(&pad, None).expect("Pad lays out");
        assert_eq!(
            (0..written.size())
                .map(|byte| written.contains(byte))
                .collect::<Vec<_>>(),
            [vec![true], vec![false; 7], vec![true; 8]].concat()
        );
        assert!(!written.covers_all());
        // `<4 x bool>` is 4 bytes: a byte store at offset 4 is past it.
        let report = scan_layout(
            "fsym_bool_vector_extent",
            None,
            vec![
                node(
                    0,
                    Inst::Alloca {
                        ty: bools,
                        count: None,
                        align: None,
                    },
                ),
                const_i64(1, 4),
                byte_gep(2, 0, 1),
                const_u8(3, 1),
                store_u8(2, 3),
            ],
        );
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
        // A GEP by `Declared` strides 16 bytes, not 1.
        let report = scan_layout(
            "fsym_declared_stride",
            None,
            vec![
                const_u64(0, 4),
                u8_alloca(1, Some(0), None),
                const_i64(2, 1),
                i64_gep(3, declared.clone(), 1, 2),
                const_u8(4, 1),
                store_u8(3, 4),
            ],
        );
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::OutOfBounds]
        );
        // `alloca Declared x (2^60 + 1)`: its byte size overflows.
        let report = scan_layout(
            "fsym_declared_alloca_overflow",
            None,
            vec![
                const_u64(0, (1 << 60) + 1),
                node(
                    1,
                    Inst::Alloca {
                        ty: declared,
                        count: Some(v(0)),
                        align: None,
                    },
                ),
            ],
        );
        assert_eq!(
            diagnostic_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::Arithmetic]
        );
    }

    /// A typed store and load of an array cost the type's description, not
    /// its bytes: the initialization a `store [u8; n]` writes and a load
    /// needs are decided from one element's coverage (the object tracked is
    /// 16 bytes). At `n = 2^63` a flag per byte could not even be reserved;
    /// the scan completes and reports the out-of-bounds accesses.
    #[test]
    fn a_huge_array_store_and_load_scan_in_the_types_size() {
        for len in [16u64, 1 << 63] {
            let array = Ty::Array(trust_ir::value::TyId::new(0), len);
            let body = vec![
                const_u64(0, 16),
                u8_alloca(1, Some(0), None),
                const_u8(2, 7),
                node(
                    3,
                    Inst::ArraySplat {
                        ty: array.clone(),
                        value: v(2),
                    },
                ),
                InstrNode::new(Inst::Store {
                    ty: array.clone(),
                    ptr: v(1),
                    value: v(3),
                    volatile: false,
                    align: None,
                }),
                load(4, array, 1, None),
                const_i64(99, 0),
                ret_i64(99),
            ];
            let mut module = test_module("fsym_huge_array_store", body);
            module.types = vec![Ty::U8];
            let kinds = diagnostic_kinds(&scan_module(&module));
            if len == 16 {
                assert!(
                    !kinds.contains(&FsymTrustIrDiagnosticKind::OutOfBounds)
                        && !kinds.contains(&FsymTrustIrDiagnosticKind::Uninitialized),
                    "len {len}: the store writes all 16 bytes the load reads: {kinds:?}"
                );
            } else {
                assert!(
                    kinds.contains(&FsymTrustIrDiagnosticKind::OutOfBounds),
                    "len {len}: {kinds:?}"
                );
            }
        }
    }

    #[test]
    fn a_type_with_no_interpreter_layout_is_refused_by_name() {
        let report = scan_layout(
            "fsym_no_layout",
            None,
            vec![node(
                0,
                Inst::Alloca {
                    ty: Ty::Struct(trust_ir::StructId::new(7)),
                    count: None,
                    align: None,
                },
            )],
        );
        assert_eq!(report.skipped_functions.len(), 1, "{report:?}");
        assert!(
            report.skipped_functions[0]
                .detail
                .contains("no reference-interpreter layout"),
            "{:?}",
            report.skipped_functions
        );
        // So is every function of a module the interpreter does not execute.
        let report = scan_layout(
            "fsym_big_endian",
            Some(trust_ir::TargetInfo {
                endianness: trust_ir::Endianness::Big,
                ..target_info("aarch64-unknown-linux-gnu", 8)
            }),
            vec![],
        );
        assert_eq!(
            report
                .skipped_functions
                .iter()
                .map(|skip| skip.reason)
                .collect::<Vec<_>>(),
            vec![FsymTrustIrSkipReason::PointerWidth]
        );
    }

    #[test]
    fn natural_alignment_places_an_allocation_too() {
        let huge = Ty::Struct(trust_ir::StructId::new(1));
        let alloc = |heap: bool| {
            node(
                0,
                if heap {
                    Inst::HeapAlloc {
                        ty: huge.clone(),
                        count: None,
                        align: None,
                        origin: trust_ir::inst::AllocOrigin::CMalloc,
                    }
                } else {
                    Inst::Alloca {
                        ty: huge.clone(),
                        count: None,
                        align: None,
                    }
                },
            )
        };
        for heap in [false, true] {
            let report = scan_layout("fsym_natural_align", None, vec![alloc(heap)]);
            assert_eq!(
                unknown_kinds(&report),
                vec![FsymTrustIrDiagnosticKind::Arithmetic],
                "{:?}",
                report.unknown_obligations
            );
            assert!(
                report.unknown_obligations[0]
                    .reason
                    .contains("natural alignment"),
                "{}",
                report.unknown_obligations[0].reason
            );
        }
    }

    #[test]
    fn materializing_a_global_owes_its_placement() {
        let huge = Ty::Struct(trust_ir::StructId::new(1));
        let global = |name: &str, ty: Ty| trust_ir::Global {
            name: name.to_string(),
            ty,
            mutable: true,
            initializer: None,
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        };
        let body = |index: u32| {
            vec![
                node(
                    0,
                    Inst::GlobalAddr {
                        global: trust_ir::value::GlobalId::new(index),
                    },
                ),
                const_i64(99, 0),
                ret_i64(99),
            ]
        };
        for (index, clean_expected) in [(0, true), (1, false)] {
            let mut module = test_module("fsym_global_placement", body(index));
            module.structs = layout_structs();
            module.globals = vec![global("G", Ty::I64), global("H", huge.clone())];
            let owed = super::fsym_owed_kinds(&module, &module.functions[0].blocks[0].body[0].inst);
            assert_eq!(
                owed,
                vec![
                    FsymTrustIrDiagnosticKind::Arithmetic,
                    FsymTrustIrDiagnosticKind::PointerArithmetic
                ]
            );
            let report = scan_module(&module);
            assert_eq!(clean(&report), clean_expected, "{report:?}");
            if !clean_expected {
                assert_eq!(
                    unknown_kinds(&report),
                    vec![
                        FsymTrustIrDiagnosticKind::Arithmetic,
                        FsymTrustIrDiagnosticKind::PointerArithmetic
                    ]
                );
            }
        }
    }

    /// The BUDGET premise is the MODULE's: a modeled placement (here a
    /// count-less, naturally aligned `alloca u8`) is Safe only when no
    /// instruction of any function — scanned or refused — places past the
    /// modeled alignment. Another function allocating past it, or
    /// materializing a global aligned past it, makes the placement an
    /// Arithmetic Unknown naming that instruction, through both entry points.
    #[test]
    fn a_placement_is_safe_only_under_the_modules_budget_premise() {
        let huge = Ty::Struct(trust_ir::StructId::new(1));
        let alloca = |align: u64| Inst::Alloca {
            ty: Ty::U8,
            count: None,
            align: Some(align),
        };
        let cases: Vec<(&str, Vec<Inst>, bool)> = vec![
            ("no other allocation", vec![], false),
            ("another placed at 4096", vec![alloca(1 << 12)], false),
            ("another placed at 8192", vec![alloca(1 << 13)], true),
            (
                "another of a type naturally aligned to 2^63",
                vec![Inst::HeapAlloc {
                    ty: huge.clone(),
                    count: None,
                    align: None,
                    origin: trust_ir::inst::AllocOrigin::CMalloc,
                }],
                true,
            ),
            (
                "a global aligned to 2^63 materialized elsewhere",
                vec![Inst::GlobalAddr {
                    global: trust_ir::value::GlobalId::new(0),
                }],
                true,
            ),
            (
                "a function fsym refuses, placing at 2^63",
                vec![Inst::Undef { ty: Ty::I64 }, alloca(1 << 63)],
                true,
            ),
        ];
        for (what, others, violates) in cases {
            let mut module = test_module(
                "fsym_budget_premise",
                vec![node(0, alloca(8)), const_i64(99, 0), ret_i64(99)],
            );
            module.structs = layout_structs();
            module.globals = vec![trust_ir::Global {
                name: "H".to_string(),
                ty: huge.clone(),
                mutable: true,
                initializer: None,
                linkage: trust_ir::Linkage::Internal,
                tls: None,
                align: None,
                section: None,
                visibility: trust_ir::Visibility::Default,
                retained: false,
            }];
            let mut other =
                Function::new(FuncId::new(1), "other", FuncTyId::new(0), BlockId::new(0));
            let mut body = others
                .into_iter()
                .enumerate()
                .map(|(index, inst)| node(10 + index as u32, inst))
                .collect::<Vec<_>>();
            body.extend([const_i64(99, 0), ret_i64(99)]);
            other.blocks = vec![Block {
                id: BlockId::new(0),
                params: vec![],
                body,
            }];
            module.functions.push(other);
            assert_eq!(
                super::budget_premise_violation(&module).is_some(),
                violates,
                "{what}: {:?}",
                super::budget_premise_violation(&module)
            );
            let scoped = super::with_fsym_module_scope(&module, || {
                super::scan_function_in_module(&module, &module.functions[0])
            });
            for report in [
                super::scan_function_in_module(&module, &module.functions[0]),
                scoped,
                {
                    let mut report = scan_module(&module);
                    report.unknown_obligations.retain(|u| u.function == "test");
                    report
                },
            ] {
                let unknowns = report
                    .unknown_obligations
                    .iter()
                    .filter(|u| u.function == "test")
                    .collect::<Vec<_>>();
                if violates {
                    assert_eq!(
                        unknowns.iter().map(|u| u.kind).collect::<Vec<_>>(),
                        vec![FsymTrustIrDiagnosticKind::Arithmetic],
                        "{what}: {report:?}"
                    );
                    assert!(
                        unknowns[0].reason.contains("BUDGET premise")
                            && unknowns[0].reason.contains("`other` bb0:"),
                        "{what}: the Unknown names the premise and the instruction breaking it: {}",
                        unknowns[0].reason
                    );
                } else {
                    assert!(unknowns.is_empty(), "{what}: {report:?}");
                }
            }
        }
    }

    /// A module scope shares the module's facts exactly while its call runs:
    /// nested scopes of one module share one entry that the outermost call
    /// removes, on return and on unwind.
    #[test]
    fn a_module_scope_shares_facts_only_while_its_call_runs() {
        let module = test_module(
            "fsym_module_scope",
            vec![
                node(
                    0,
                    Inst::Alloca {
                        ty: Ty::U8,
                        count: None,
                        align: Some(1 << 13),
                    },
                ),
                const_i64(99, 0),
                ret_i64(99),
            ],
        );
        let open = |module: &Module| {
            let (address, _) = super::module_scope_key(module);
            super::open_module_scopes()
                .iter()
                .filter(|scope| scope.module == address)
                .map(|scope| scope.depth)
                .sum::<usize>()
        };
        super::with_fsym_module_scope(&module, || {
            super::with_fsym_module_scope(&module, || {
                assert_eq!(open(&module), 2);
                let report = super::scan_function_in_module(&module, &module.functions[0]);
                assert_eq!(
                    report
                        .unknown_obligations
                        .iter()
                        .filter(|u| u.kind == FsymTrustIrDiagnosticKind::Arithmetic)
                        .count(),
                    1,
                    "the 8192 placement itself"
                );
            });
            assert_eq!(open(&module), 1);
        });
        assert_eq!(open(&module), 0, "the outermost call removes the entry");
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            super::with_fsym_module_scope(&module, || panic!("a scan panics"));
        }));
        assert!(unwound.is_err());
        assert_eq!(open(&module), 0, "an unwinding call removes the entry too");
    }

    /// Round 7: the round-6 scope was a guard; `mem::forget` of it left the
    /// scope open, and a module then edited in place (pointer and length of
    /// its function table unchanged) was served the stale premise — both
    /// `scan_function_in_module` and `scan_module` claimed `f`'s placement
    /// clean while another function now placed past 4096. The scope is a
    /// call now: nothing outlives it, so an edit after it is decided afresh.
    #[test]
    fn a_module_edited_after_its_scope_is_decided_afresh() {
        let mut module = test_module(
            "fsym_module_scope_edit",
            vec![
                node(
                    0,
                    Inst::Alloca {
                        ty: Ty::U8,
                        count: None,
                        align: Some(8),
                    },
                ),
                const_i64(99, 0),
                ret_i64(99),
            ],
        );
        let mut other = Function::new(FuncId::new(1), "other", FuncTyId::new(0), BlockId::new(0));
        other.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![const_i64(10, 0), const_i64(99, 0), ret_i64(99)],
        }];
        module.functions.push(other);
        let table = (module.functions.as_ptr(), module.functions.len());
        super::with_fsym_module_scope(&module, || {
            assert!(clean(&super::scan_function_in_module(
                &module,
                &module.functions[0]
            )));
        });
        // In place: the function table neither moves nor changes length.
        module.functions[1].blocks[0].body[0] = node(
            10,
            Inst::Alloca {
                ty: Ty::U8,
                count: None,
                align: Some(1 << 13),
            },
        );
        assert_eq!(
            table,
            (module.functions.as_ptr(), module.functions.len()),
            "the edit is in place"
        );
        let scanned = super::scan_function_in_module(&module, &module.functions[0]);
        let mut whole = scan_module(&module);
        whole.unknown_obligations.retain(|u| u.function == "test");
        for report in [scanned, whole] {
            assert_eq!(
                unknown_kinds(&report),
                vec![FsymTrustIrDiagnosticKind::Arithmetic],
                "{report:?}"
            );
            assert!(
                report.unknown_obligations[0]
                    .reason
                    .contains("`other` bb0:0"),
                "{}",
                report.unknown_obligations[0].reason
            );
        }
    }

    #[test]
    fn a_whole_aggregate_store_leaves_its_padding_uninitialized() {
        let pad = Ty::Struct(trust_ir::StructId::new(2));
        // Fill the slot, store a `Pad` over it (un-initializing bytes 1..8),
        // then read bytes 1..9.
        let body = |read_at: i64| {
            vec![
                node(
                    0,
                    Inst::Alloca {
                        ty: pad.clone(),
                        count: None,
                        align: None,
                    },
                ),
                const_u8(1, 7),
                const_u64(2, 16),
                memset(0, 1, 2),
                node(
                    3,
                    Inst::Const {
                        ty: pad.clone(),
                        value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]),
                    },
                ),
                InstrNode::new(Inst::Store {
                    ty: pad.clone(),
                    ptr: v(0),
                    value: v(3),
                    volatile: false,
                    align: None,
                }),
                const_i64(4, read_at),
                byte_gep(5, 0, 4),
                load(6, Ty::U8, 5, None),
                // The whole value reads only its live fields.
                load(7, pad.clone(), 0, None),
            ]
        };
        let report = scan_layout("fsym_padding_read", None, body(1));
        assert_eq!(
            unknown_kinds(&report),
            vec![FsymTrustIrDiagnosticKind::Uninitialized],
            "{:?}",
            report.unknown_obligations
        );
        assert_eq!(report.unknown_obligations[0].inst_index, 8);
        // A live field's byte is initialized, and so is the whole value.
        assert!(clean(&scan_layout("fsym_field_read", None, body(8))));
    }

    /// Round 7: on a 32-bit target a non-empty object may end exactly at
    /// 2^32 (the interpreter refuses only a placement whose LAST byte is past
    /// the address space, and nothing keeps the bump pointer below it), where
    /// a pointer one past it has no address: a GEP to the end, a GEP from the
    /// end (by zero, or with no index) and exposing the end are Unknown there
    /// — Safe at 64 bits, where an object never ends past 2^64 - 1. Its last
    /// byte and its base are named on both.
    #[test]
    fn one_past_the_end_is_nameable_only_where_the_address_space_cannot_end_there() {
        let wasm32 = || Some(target_info("wasm32-unknown-unknown", 4));
        let x86_64 = || Some(target_info("x86_64-unknown-linux-gnu", 8));
        let pointer_unknowns = |report: &super::FsymTrustIrReport| {
            report
                .unknown_obligations
                .iter()
                .filter(|u| u.kind == FsymTrustIrDiagnosticKind::PointerArithmetic)
                .map(|u| u.inst_index)
                .collect::<Vec<_>>()
        };
        // p = alloca u8 x 16; q = gep p, AT; (then `tail`)
        let body = |at: i128, tail: Vec<InstrNode>| {
            let mut body = vec![
                usize_const(0, 16),
                u8_alloca(1, Some(0), None),
                const_i64(2, at as i64),
                i64_gep(3, Ty::U8, 1, 2),
            ];
            body.extend(tail);
            body
        };
        let zero_gep = || vec![const_i64(4, 0), i64_gep(5, Ty::U8, 3, 4)];
        let no_index_gep = || {
            vec![node(
                4,
                Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: v(3),
                    indices: vec![],
                    inbounds: false,
                },
            )]
        };
        let exposed = || vec![cast(5, trust_ir::CastOp::PtrToInt, Ty::Ptr, Ty::Usize, 3)];
        for (what, report, unknown_at) in [
            (
                "gep to the end",
                scan_pinned("end", wasm32(), body(16, vec![])),
                vec![3],
            ),
            (
                "gep to the last byte",
                scan_pinned("last", wasm32(), body(15, vec![])),
                vec![],
            ),
            (
                "gep to the base",
                scan_pinned("base", wasm32(), body(0, vec![])),
                vec![],
            ),
            (
                "gep by zero from the end",
                scan_pinned("end0", wasm32(), body(16, zero_gep())),
                vec![3, 5],
            ),
            (
                "gep with no index from the end",
                scan_pinned("endnone", wasm32(), body(16, no_index_gep())),
                vec![3, 4],
            ),
            (
                "the end exposed",
                scan_pinned("endexp", wasm32(), body(16, exposed())),
                vec![3, 4],
            ),
            (
                "the last byte exposed",
                scan_pinned("lastexp", wasm32(), body(15, exposed())),
                vec![],
            ),
            (
                "the end exposed at 64 bits",
                scan_pinned("endexp64", x86_64(), body(16, exposed())),
                vec![],
            ),
            (
                "gep by zero from the end at 64 bits",
                scan_pinned("end064", x86_64(), body(16, zero_gep())),
                vec![],
            ),
        ] {
            assert!(report.diagnostics.is_empty(), "{what}: {report:?}");
            assert_eq!(pointer_unknowns(&report), unknown_at, "{what}: {report:?}");
            assert_eq!(
                report.unknown_obligations.len(),
                unknown_at.len(),
                "{what}: {report:?}"
            );
        }
    }

    /// Round 7: at 32-bit pointers no placement overflows 64 bits, whatever
    /// its alignment — the interpreter refuses (OutOfMemory) one whose last
    /// byte leaves the address space, before its next address could — so an
    /// allocation placed past 4096 is Safe there and breaks no premise of the
    /// module's other placements. At 64 bits both stay Unknown.
    #[test]
    fn a_32_bit_placement_rests_on_no_alignment_premise() {
        for (target, clean_expected) in [
            (Some(target_info("wasm32-unknown-unknown", 4)), true),
            (Some(target_info("x86_64-unknown-linux-gnu", 8)), false),
        ] {
            let report = scan_pinned(
                "placement32",
                target,
                vec![
                    u8_alloca(0, None, Some(1 << 13)),
                    u8_alloca(1, None, Some(8)),
                ],
            );
            assert_eq!(clean(&report), clean_expected, "{report:?}");
            if !clean_expected {
                assert_eq!(
                    report
                        .unknown_obligations
                        .iter()
                        .map(|u| (u.kind, u.inst_index))
                        .collect::<Vec<_>>(),
                    vec![
                        (FsymTrustIrDiagnosticKind::Arithmetic, 0),
                        (FsymTrustIrDiagnosticKind::Arithmetic, 1)
                    ],
                    "{report:?}"
                );
            }
        }
    }

    #[test]
    fn pointer_comparison_checks_each_operand_before_its_result_is_used() {
        for target in [
            target_info("wasm32-unknown-unknown", 4),
            target_info("aarch64-apple-darwin", 8),
        ] {
            for (lhs, rhs) in [(v(0), v(1)), (v(1), v(0))] {
                let mut module = test_module_blocks(
                    "pointer_comparison_parameter",
                    vec![Block {
                        id: BlockId::new(0),
                        params: vec![(v(0), Ty::Ptr)],
                        body: vec![
                            InstrNode::new(Inst::NullPtr).with_result(v(1)),
                            InstrNode::new(Inst::ICmp {
                                op: ICmpOp::Eq,
                                ty: Ty::Ptr,
                                lhs,
                                rhs,
                            })
                            .with_result(v(2)),
                            const_i64(99, 0),
                            ret_i64(99),
                        ],
                    }],
                );
                module.func_types[0].params = vec![Ty::Ptr];
                module.target_info = Some(target.clone());
                assert!(trust_ir_build::validate_module(&module).is_empty());
                assert_eq!(
                    site_opcodes(super::reachable_obligation_sites(
                        &module,
                        &module.functions[0].blocks[0],
                    )),
                    vec![(1, "ICmp")]
                );
                let report = scan_module(&module);
                assert_eq!(report.scanned_functions, 1, "{report:?}");
                assert!(report.diagnostics.is_empty(), "{report:?}");
                assert_eq!(
                    report
                        .unknown_obligations
                        .iter()
                        .map(|u| (u.kind, u.inst_index))
                        .collect::<Vec<_>>(),
                    vec![(FsymTrustIrDiagnosticKind::PointerArithmetic, 1)],
                    "both operand positions must check an unknown address: {report:?}"
                );
            }
        }
    }

    #[test]
    fn pointer_comparison_known_addresses_and_integer_comparisons_remain_clean() {
        for target in [
            target_info("wasm32-unknown-unknown", 4),
            target_info("aarch64-apple-darwin", 8),
        ] {
            for (ty, values) in [
                (
                    Ty::Ptr,
                    vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(0)),
                        InstrNode::new(Inst::NullPtr).with_result(v(1)),
                    ],
                ),
                (Ty::U64, vec![const_u64(0, 0), const_u64(1, 1)]),
            ] {
                let mut body = values;
                body.push(
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: ty.clone(),
                        lhs: v(0),
                        rhs: v(1),
                    })
                    .with_result(v(2)),
                );
                let report = scan_pinned("pointer_comparison_known", Some(target.clone()), body);
                assert_eq!(report.scanned_functions, 1, "{report:?}");
                assert!(clean(&report), "{ty:?}: {report:?}");
            }
        }
    }

    /// Round 7: a parameter's address is never proven one the interpreter
    /// computes. A caller's 64-bit GEP moves an allocation OFFSET, faulting
    /// only when that overflows u64, so it can hand over a pointer whose
    /// base + offset has no address (and an embedder can hand an entry one
    /// naming no allocation at all): `f(p) { ptrtoint p }` and
    /// `f(p) { store p }` scanned clean on x86_64 while the interpreter faults
    /// ("PtrToInt: pointer address overflow", "unknown allocation 7"). A GEP
    /// result's address is proven only where the GEP's no-wrap is: `gep p,
    /// u64::MAX` then `ptrtoint` recorded the cast Safe (an exact 64-bit
    /// address is its own representation) while the interpreter faulted at
    /// it. A constant address stays nameable.
    #[test]
    fn exposing_an_address_needs_one_the_interpreter_computes() {
        let x86_64 = || Some(target_info("x86_64-unknown-linux-gnu", 8));
        let scan = |name: &str, body: Vec<InstrNode>| {
            let mut body = body;
            body.extend([const_i64(99, 0), ret_i64(99)]);
            let mut module = test_module_blocks(
                name,
                vec![Block {
                    id: BlockId::new(0),
                    params: vec![(v(0), Ty::Ptr)],
                    body,
                }],
            );
            module.target_info = x86_64();
            scan_module(&module)
        };
        let exposure_unknowns = |report: &super::FsymTrustIrReport| {
            report
                .unknown_obligations
                .iter()
                .filter(|u| u.kind == FsymTrustIrDiagnosticKind::PointerArithmetic)
                .map(|u| u.inst_index)
                .collect::<Vec<_>>()
        };
        let ptrtoint_param = scan("ptrtoint_param", vec![ptrtoint(1, 0)]);
        assert_eq!(
            exposure_unknowns(&ptrtoint_param),
            vec![0],
            "{ptrtoint_param:?}"
        );
        let store_param = scan(
            "store_param",
            vec![
                node(
                    1,
                    Inst::Alloca {
                        ty: Ty::Ptr,
                        count: None,
                        align: None,
                    },
                ),
                InstrNode::new(Inst::Store {
                    ty: Ty::Ptr,
                    ptr: v(1),
                    value: v(0),
                    volatile: false,
                    align: None,
                }),
            ],
        );
        assert_eq!(exposure_unknowns(&store_param), vec![1], "{store_param:?}");
        // gep p, u64::MAX; ptrtoint: the cast owes its own Unknown.
        let wrapped = scan(
            "wrapped",
            vec![
                const_u64(1, u64::MAX),
                i64_gep(2, Ty::U8, 0, 1),
                ptrtoint(3, 2),
            ],
        );
        assert_eq!(exposure_unknowns(&wrapped), vec![1, 2], "{wrapped:?}");
        // An integer turned into a pointer has a nameable address, but a GEP
        // of it past the address space moves only the offset: exposing the
        // result owes its own Unknown.
        let integer = scan(
            "integer",
            vec![
                const_u64(1, 0x1000),
                cast(2, trust_ir::CastOp::PtrToInt, Ty::Ptr, Ty::U64, 0),
                cast(3, trust_ir::CastOp::IntToPtr, Ty::U64, Ty::Ptr, 2),
                const_u64(4, u64::MAX),
                i64_gep(5, Ty::U8, 3, 4),
                ptrtoint(6, 5),
            ],
        );
        assert_eq!(exposure_unknowns(&integer), vec![1, 4, 5], "{integer:?}");
        // A constant address and a GEP of it proven not to wrap stay exact.
        let constant = scan(
            "constant",
            vec![
                const_u64(1, 0x1000),
                cast(2, trust_ir::CastOp::IntToPtr, Ty::U64, Ty::Ptr, 1),
                const_u64(3, 8),
                i64_gep(4, Ty::U8, 2, 3),
                ptrtoint(5, 4),
            ],
        );
        assert!(clean(&constant), "{constant:?}");
    }

    #[test]
    fn a_wasm32_gep_candidate_decides_the_32_bit_address_space() {
        // `q = gep i64, alloca, x; r = gep u8, q, 0xFFFFFFFF` on wasm32: the
        // result is past the address space whatever `x`; the 64-bit offset
        // condition alone must never be a candidate for it.
        let report = scan_module(&{
            let mut module = test_module_blocks(
                "fsym_wasm32_gep_chain",
                vec![Block {
                    id: BlockId::new(0),
                    params: vec![(v(0), Ty::U8)],
                    body: vec![
                        usize_const(1, 16),
                        node(
                            2,
                            Inst::Alloca {
                                ty: Ty::U64,
                                count: Some(v(1)),
                                align: Some(16),
                            },
                        ),
                        i64_gep(3, Ty::I64, 2, 0),
                        usize_const(4, 0xFFFF_FFFF),
                        i64_gep(5, Ty::U8, 3, 4),
                        const_i64(99, 0),
                        ret_i64(99),
                    ],
                }],
            );
            module.target_info = Some(target_info("wasm32-unknown-unknown", 4));
            module
        });
        let geps = report
            .unknown_obligations
            .iter()
            .filter(|unknown| unknown.kind == FsymTrustIrDiagnosticKind::PointerArithmetic)
            .collect::<Vec<_>>();
        assert_eq!(geps.len(), 2, "{:?}", report.unknown_obligations);
        assert!(
            geps.iter()
                .all(|unknown| unknown.solver_candidate.is_none()),
            "{geps:?}"
        );
        // An exact address (a pointer parameter's) carries a candidate at the
        // target's limit.
        let report = scan_module(&{
            let mut module = test_module_blocks(
                "fsym_wasm32_gep_address",
                vec![Block {
                    id: BlockId::new(0),
                    params: vec![(v(0), Ty::U8), (v(2), Ty::Ptr)],
                    body: vec![i64_gep(3, Ty::U8, 2, 0), const_i64(99, 0), ret_i64(99)],
                }],
            );
            module.target_info = Some(target_info("wasm32-unknown-unknown", 4));
            module
        });
        let candidate = report
            .unknown_obligations
            .iter()
            .find(|unknown| unknown.kind == FsymTrustIrDiagnosticKind::PointerArithmetic)
            .and_then(|unknown| unknown.solver_candidate.clone());
        assert!(
            matches!(
                candidate.map(|candidate| candidate.obligation),
                Some(FsymTrustIrSolverObligation::Arithmetic {
                    kind: ArithUbKind::GepOffset {
                        limit: 0xFFFF_FFFF,
                        ..
                    },
                    ..
                })
            ),
            "{:?}",
            report.unknown_obligations
        );
    }

    #[test]
    fn an_annotation_on_a_parameter_access_is_a_claim_never_a_proof() {
        // `store u8 %p, 1 [NotNull, InBounds]` through a parameter: every
        // caller-dependent obligation stays open.
        let report = scan_with_params(
            "fsym_annotated_param",
            vec![(v(0), Ty::Ptr)],
            vec![
                const_u8(1, 1),
                store_u8(0, 1)
                    .with_proof(trust_ir::ProofAnnotation::NotNull)
                    .with_proof(trust_ir::ProofAnnotation::InBounds),
            ],
        );
        let kinds = unknown_kinds(&report);
        for kind in [
            FsymTrustIrDiagnosticKind::NullDeref,
            FsymTrustIrDiagnosticKind::OutOfBounds,
            FsymTrustIrDiagnosticKind::UseAfterFree,
        ] {
            assert!(kinds.contains(&kind), "{kind:?} not owed: {kinds:?}");
        }
    }

    /// Round 8 (the round-7 verifier): a placement whose own footprint
    /// reaches the 2^62-byte bound fsym decides placements below is decided
    /// on nothing but that bound. Measured before trust-ir v50: `alloca u8 x
    /// u64::MAX` scanned clean on wasm32 and x86_64 while the interpreter,
    /// given an unbounded memory budget, faulted "Alloca: next address
    /// overflow"; at 32 bits `alloca u8 x 2^63, align 2^63` faulted the same
    /// way. (Since v50 the interpreter has no budget and that fault is
    /// `OutOfMemory`, so the bound only narrows what fsym decides.) Every
    /// such placement — counted, count-less of a
    /// type that large, a heap block its 16 bytes of usable-size slack carry
    /// there, a global that large — is an Unknown naming the bound; one byte
    /// below it stays Safe.
    #[test]
    fn a_placement_as_large_as_the_run_models_budget_is_unknown() {
        const BOUND: u64 = 1 << 62;
        let array = |len: u64| Ty::Array(trust_ir::TyId::new(0), len);
        let heap = |ty: Ty, count: Option<u32>| {
            node(
                1,
                Inst::HeapAlloc {
                    ty,
                    count: count.map(v),
                    align: None,
                    origin: trust_ir::inst::AllocOrigin::CMalloc,
                },
            )
        };
        let global = |len: u64| trust_ir::Global {
            name: "G".to_string(),
            ty: array(len),
            mutable: true,
            initializer: None,
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        };
        let global_addr = || {
            node(
                1,
                Inst::GlobalAddr {
                    global: trust_ir::value::GlobalId::new(0),
                },
            )
        };
        for target in [
            target_info("wasm32-unknown-unknown", 4),
            target_info("x86_64-unknown-linux-gnu", 8),
        ] {
            let mut cases: Vec<(String, Vec<InstrNode>, Vec<trust_ir::Global>, bool)> = Vec::new();
            for (count, clean_expected) in [(u64::MAX, false), (BOUND, false), (BOUND - 1, true)] {
                cases.push((
                    format!("alloca u8 x {count:#x}"),
                    vec![const_u64(0, count), u8_alloca(1, Some(0), Some(1))],
                    vec![],
                    clean_expected,
                ));
            }
            for (len, clean_expected) in [(BOUND, false), (BOUND - 1, true)] {
                cases.push((
                    format!("alloca [u8; {len:#x}]"),
                    vec![node(
                        1,
                        Inst::Alloca {
                            ty: array(len),
                            count: None,
                            align: None,
                        },
                    )],
                    vec![],
                    clean_expected,
                ));
            }
            // The heap's usable-size slack is part of the footprint.
            for (len, clean_expected) in [(BOUND - 16, false), (BOUND - 17, true)] {
                cases.push((
                    format!("heap u8 x {len:#x}"),
                    vec![const_u64(0, len), heap(Ty::U8, Some(0))],
                    vec![],
                    clean_expected,
                ));
                cases.push((
                    format!("heap [u8; {len:#x}]"),
                    vec![heap(array(len), None)],
                    vec![],
                    clean_expected,
                ));
            }
            for (len, clean_expected) in [(BOUND, false), (BOUND - 1, true)] {
                cases.push((
                    format!("global [u8; {len:#x}]"),
                    vec![global_addr()],
                    vec![global(len)],
                    clean_expected,
                ));
            }
            if target.pointer_size == 4 {
                // At 32 bits a placement at any alignment is Safe below the
                // bound: the base is at most 2^63.
                for (count, clean_expected) in [(1 << 63, false), (BOUND - 1, true)] {
                    cases.push((
                        format!("alloca u8 x {count:#x}, align 2^63"),
                        vec![const_u64(0, count), u8_alloca(1, Some(0), Some(1 << 63))],
                        vec![],
                        clean_expected,
                    ));
                }
            }
            for (what, mut body, globals, clean_expected) in cases {
                let placement = body.len() - 1;
                body.extend([const_i64(99, 0), ret_i64(99)]);
                let mut module = test_module("fsym_footprint", body);
                module.target_info = Some(target.clone());
                module.types = vec![Ty::U8];
                module.globals = globals;
                let report = scan_module(&module);
                assert_eq!(
                    clean(&report),
                    clean_expected,
                    "{} {what}: {report:?}",
                    target.triple
                );
                if !clean_expected {
                    assert!(
                        report.unknown_obligations.iter().any(|u| {
                            u.kind == FsymTrustIrDiagnosticKind::Arithmetic
                                && u.inst_index == placement
                                && (u.reason.contains("fsym decides placements below")
                                    || u.reason.contains("past 2^64"))
                        }),
                        "{} {what}: the placement's Unknown names the bound: {:?}",
                        target.triple,
                        report.unknown_obligations
                    );
                }
            }
        }
    }

    /// Round 8: the run model is checkable. A run's options must stay below
    /// its fuel bound, and no entry argument may carry an
    /// allocation pointer or a runtime handle, however deep; the
    /// interpreter's default options, integers, null, dangling addresses and
    /// fat pointers of them are inside it.
    #[test]
    fn the_run_model_admits_exactly_its_runs() {
        use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind};
        let model = super::FSYM_RUN_MODEL;
        let options = InterpretOptions::default();
        let int = InterpretValue::int(Ty::U64, 7).expect("u64");
        let null = InterpretValue {
            ty: Ty::Ptr,
            kind: InterpretValueKind::NullPtr,
        };
        let dangling = InterpretValue {
            ty: Ty::Ptr,
            kind: InterpretValueKind::DanglingPtr(0x1000),
        };
        let forged = InterpretValue {
            ty: Ty::Ptr,
            kind: InterpretValueKind::Ptr(trust_ir::interpret::InterpretPointer {
                allocation: 0,
                offset: 0,
            }),
        };
        let handle = InterpretValue {
            ty: Ty::I64,
            kind: InterpretValueKind::Handle { id: 0 },
        };
        let fat = |data: &InterpretValue| InterpretValue {
            ty: Ty::FatPtr(FatPtrKind::Str),
            kind: InterpretValueKind::FatPtr {
                data: Box::new(data.clone()),
                metadata: Box::new(int.clone()),
            },
        };
        let tuple = |value: &InterpretValue| InterpretValue {
            ty: Ty::Tuple(vec![Ty::U64, value.ty.clone()]),
            kind: InterpretValueKind::Aggregate(vec![int.clone(), value.clone()]),
        };
        // Sequence and set values are ropes (trust-ir f9a59d5e): a forged
        // part is found in an element list and in a splat's one stored value.
        let elem_ty = trust_ir::value::TyId::new(0);
        let sequence = |values: Vec<InterpretValue>| InterpretValue {
            ty: Ty::Sequence(elem_ty),
            kind: InterpretValueKind::Sequence(trust_ir::interpret::ArrayValue::from_vec(values)),
        };
        let set_splat = |value: &InterpretValue, len: u64| InterpretValue {
            ty: Ty::Set(elem_ty, trust_ir::SetRepr::Boxed),
            kind: InterpretValueKind::Set(trust_ir::interpret::ArrayValue::splat(
                value.clone(),
                len,
            )),
        };
        assert_eq!(model.breach(&options, &[]), None);
        assert_eq!(
            model.breach(
                &options,
                &[int.clone(), null.clone(), dangling.clone(), fat(&dangling)]
            ),
            None
        );
        assert_eq!(
            model.breach(
                &options,
                &[
                    sequence(vec![int.clone(), null.clone(), fat(&dangling)]),
                    set_splat(&int, 1 << 40),
                    sequence(Vec::new()),
                ]
            ),
            None
        );
        let largest = InterpretOptions {
            fuel: model.fuel_limit - 1,
            max_call_depth: u64::MAX,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        };
        assert_eq!(model.breach(&largest, &[]), None);
        // trust-ir v56: a run under `PanicStrategy::Unwind` is outside the
        // panic=abort run model, whatever its fuel and arguments.
        let unwind = InterpretOptions {
            panic_strategy: trust_ir::interpret::PanicStrategy::Unwind,
            ..options
        };
        assert!(
            model
                .breach(&unwind, &[])
                .is_some_and(|why| why.contains("Unwind")),
            "{unwind:?}"
        );
        for past in [
            InterpretOptions {
                fuel: model.fuel_limit,
                ..options
            },
            InterpretOptions {
                fuel: u64::MAX,
                ..options
            },
        ] {
            assert!(model.breach(&past, &[]).is_some(), "{past:?}");
        }
        for arg in [
            forged.clone(),
            handle.clone(),
            fat(&forged),
            tuple(&forged),
            tuple(&tuple(&handle)),
            sequence(vec![int.clone(), forged.clone()]),
            sequence(vec![tuple(&handle)]),
            set_splat(&forged, 1 << 40),
            set_splat(&tuple(&handle), 3),
        ] {
            assert!(
                model
                    .breach(&options, &[int.clone(), arg.clone()])
                    .is_some(),
                "{arg:?}"
            );
        }
        let report = scan_module(&test_module(
            "fsym_run_model",
            vec![const_i64(99, 0), ret_i64(99)],
        ));
        assert_eq!(report.run_model(), model);
    }

    /// Round 8: the BUDGET premise bounds a run's placements by its fuel
    /// only where each placement costs a step. A `SeqMap` through a
    /// function with no body places an element cell per element, and a host
    /// model serves each call with no step: a module holding one breaks the
    /// premise (as an unresolved element function does), and the placement
    /// of a function it never calls is an Unknown naming it.
    #[test]
    fn a_seq_map_through_a_function_with_no_body_breaks_the_budget_premise() {
        let cell = Ty::RefMut(Box::new(Ty::U8));
        for (fwd_body, violates) in [(true, false), (false, true)] {
            let mut module = test_module(
                "fsym_seq_map_premise",
                vec![u8_alloca(0, None, Some(8)), const_i64(99, 0), ret_i64(99)],
            );
            module.types = vec![Ty::U8];
            module.func_types.push(FuncTy {
                params: vec![cell.clone()],
                returns: vec![],
                abi: None,
                is_vararg: false,
            });
            let mut fwd = Function::new(FuncId::new(1), "fwd", FuncTyId::new(1), BlockId::new(0));
            if fwd_body {
                fwd.blocks = vec![Block {
                    id: BlockId::new(0),
                    params: vec![(v(0), cell.clone())],
                    body: vec![InstrNode::new(Inst::Return { values: vec![] })],
                }];
            }
            module.functions.push(fwd);
            let mut other =
                Function::new(FuncId::new(2), "other", FuncTyId::new(0), BlockId::new(0));
            other.blocks = vec![Block {
                id: BlockId::new(0),
                params: vec![(v(10), Ty::Sequence(trust_ir::TyId::new(0)))],
                body: vec![
                    node(
                        11,
                        Inst::SeqMap {
                            ty: Ty::Sequence(trust_ir::TyId::new(0)),
                            seq: v(10),
                            fwd: FuncId::new(1),
                        },
                    ),
                    const_i64(99, 0),
                    ret_i64(99),
                ],
            }];
            module.functions.push(other);
            let violation = super::budget_premise_violation(&module);
            assert_eq!(violation.is_some(), violates, "{violation:?}");
            let report = super::scan_function_in_module(&module, &module.functions[0]);
            assert_eq!(clean(&report), !violates, "{report:?}");
            if violates {
                assert!(
                    report.unknown_obligations[0]
                        .reason
                        .contains("`other` bb0:0")
                        && report.unknown_obligations[0].reason.contains("no body"),
                    "{:?}",
                    report.unknown_obligations
                );
            }
        }
    }
}
