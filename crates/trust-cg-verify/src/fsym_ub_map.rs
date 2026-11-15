// Symbolic execution: the interpreter-derived UB obligation map of the bounded trust_ir scanner
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Every undefined behaviour trust-ir's reference interpreter can raise, the
//! instructions that raise it, and what the bounded fsym scanner owes for it.
//!
//! The reference interpreter (`trust_ir::interpret`, at the rev this workspace
//! pins in `Cargo.lock`) is trust-ir's executable semantics. Each
//! place it constructs an `UndefinedBehavior` error is one entry of
//! [`FSYM_INTERPRETER_UB_SITES`], keyed by the interpreter function that builds
//! the error and the start of its message. Each entry names the
//! [`FSYM_TRUST_IR_UB_CLASSES`](crate::fsym_trust_ir::FSYM_TRUST_IR_UB_CLASSES)
//! class it belongs to and, per group of raising instructions
//! (`Inst` variant names, see [`fsym_inst_variant_name`]), a stance:
//!
//! * [`FsymUbStance::Owed`]: fsym owes a verdict of that kind at every admitted
//!   instruction of the group whose shape can raise it
//!   (`fsym_trust_ir::fsym_owed_kinds`, which the per-block deref-coverage
//!   invariant enforces at scan time: a site that owes a kind and records no
//!   verdict for it is a coverage error, never a pass);
//! * [`FsymUbStance::Refused`]: every instruction of the group is refused at
//!   admission;
//! * [`FsymUbStance::AtSource`]: the UB inspects a value made elsewhere (poison),
//!   and the verdict is owed where that value is made;
//! * [`FsymUbStance::NotRaised`] / [`FsymUbStance::Outside`]: the site cannot
//!   arise from that group in a scanned function, or is not UB of a scanned
//!   body (the harness's entry arguments, a host model, a pointer the
//!   embedder forged: [`FORGED_ENTRY_POINTER`]), with the reason. An
//!   instruction's `Outside` names a run outside fsym's run model
//!   (`fsym_trust_ir::FSYM_RUN_MODEL`, which `FsymRunModel::breach`
//!   decides): a forged entry pointer. (Since trust-ir v50 the interpreter
//!   has no memory budget and exhausting the address space is
//!   `OutOfMemory`, not UB, so no placement raises UB past a budget.)
//!
//! THE ADMISSION GATE CONSULTS THIS MAP ([`fsym_map_refusal`]): an instruction
//! is admitted only if fsym owes a verdict for every UB it can raise; otherwise
//! it is refused by name (the site's message and class). `tests/fsym_ub_map.rs`
//! re-derives the site list and each site's raising instructions from the
//! interpreter's source (a call graph from `execute_node`'s arms) and fails on
//! any difference, so a new interpreter UB, a UB newly reachable from an
//! instruction, or a newly admitted instruction cannot slip through; and it
//! checks the classes table against the map, so the table can never again
//! claim a class is impossible or refused when an admitted instruction raises
//! it.

use crate::fsym_trust_ir::{
    FSYM_TRUST_IR_UB_CLASSES, FsymTrustIrDiagnosticKind, FsymUbClassStatus, fsym_owed_kinds,
    is_bulk_memory_call, is_pointer_like_ty, materializes_global, ty_may_hold_address,
};
use std::collections::HashMap;
use std::sync::OnceLock;
use trust_ir::{BinOp, CastOp, Inst, Module, Ty};

/// Pseudo-raiser: the interpreter's entry (`execute_function`): its entry
/// arguments, and a body-less entry run through a host model.
pub const RAISER_ENTRY: &str = "<entry>";
/// Pseudo-raiser: the block walk (`execute_function_inner`): binding block
/// parameters, checking returned values.
pub const RAISER_WALK: &str = "<walk>";
/// Pseudo-site function: a callee's body executed by a call
/// (`execute_callee`), with the message [`CALLEE_BODY`].
pub const CALLEE_FUNCTION: &str = "execute_callee";
/// Pseudo-site message: whatever UB the callee's execution raises.
pub const CALLEE_BODY: &str = "<callee body>";

/// What fsym does about one interpreter UB site, for one group of raisers.
#[derive(Debug, Clone, Copy)]
pub enum FsymUbStance {
    /// A verdict of `kind` is owed at every admitted raiser whose shape
    /// `applies` accepts; `otherwise` says why the site cannot arise from any
    /// other shape.
    Owed {
        kind: FsymTrustIrDiagnosticKind,
        applies: fn(&Module, &Inst) -> bool,
        otherwise: &'static str,
    },
    /// Every raiser in the group is refused at admission.
    Refused,
    /// The UB inspects a value made elsewhere; a verdict of `kind` is owed
    /// where that value is made (`detail` names where).
    AtSource {
        kind: FsymTrustIrDiagnosticKind,
        detail: &'static str,
    },
    /// The call graph reaches the site from this group, but it cannot arise
    /// there in a scanned function: `detail` says why.
    NotRaised(&'static str),
    /// Not UB of a scanned function's body: `detail` says why.
    Outside(&'static str),
}

/// One group of raisers of a site and fsym's stance for them.
#[derive(Debug, Clone, Copy)]
pub struct FsymUbRaise {
    /// `Inst` variant names ([`fsym_inst_variant_name`]) or pseudo-raisers
    /// ([`RAISER_ENTRY`], [`RAISER_WALK`]).
    pub by: &'static [&'static str],
    pub stance: FsymUbStance,
}

/// One place the reference interpreter raises `UndefinedBehavior`.
#[derive(Debug, Clone, Copy)]
pub struct FsymInterpreterUbSite {
    /// The interpreter function that builds the error.
    pub function: &'static str,
    /// The start of its message literal (unique within `function`).
    pub message: &'static str,
    /// The `FSYM_TRUST_IR_UB_CLASSES` class it belongs to.
    pub class: &'static str,
    /// Every raiser, grouped by stance. Their union is exactly the set the
    /// interpreter's call graph reaches the site from.
    pub raisers: &'static [FsymUbRaise],
}

// ---------------------------------------------------------------------------
// Shapes: which instances of a raising variant can raise a site
// ---------------------------------------------------------------------------

fn always(_: &Module, _: &Inst) -> bool {
    true
}

fn allocation_with_count(_: &Module, inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Alloca { count: Some(_), .. } | Inst::HeapAlloc { count: Some(_), .. }
    )
}

/// `GlobalAddr`, or a `Const` addressing a symbol: it materializes (places
/// and initializes) a module global.
fn global_materializer(_: &Module, inst: &Inst) -> bool {
    materializes_global(inst)
}

fn memcpy_semantics(_: &Module, inst: &Inst) -> bool {
    matches!(inst, Inst::MemCopy { overlap: false, .. })
}

fn raw_float_to_int(_: &Module, inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Cast {
            op: CastOp::FPToSI | CastOp::FPToUI,
            ..
        }
    )
}

fn pointer_integer_cast(_: &Module, inst: &Inst) -> bool {
    matches!(inst, Inst::Cast { src_ty, dst_ty, .. } if is_pointer_like_ty(src_ty) != is_pointer_like_ty(dst_ty))
}

fn pointer_comparison(_: &Module, inst: &Inst) -> bool {
    matches!(inst, Inst::ICmp { ty: Ty::Ptr, .. })
}

fn stores_address(module: &Module, inst: &Inst) -> bool {
    match inst {
        Inst::Store { ty, .. }
        | Inst::AtomicStore { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::CmpXchg { ty, .. } => ty_may_hold_address(module, ty),
        _ => false,
    }
}

fn runs_a_callee(module: &Module, inst: &Inst) -> bool {
    matches!(inst, Inst::Call { .. }) && !is_bulk_memory_call(module, inst)
}

fn binop_is(inst: &Inst, ops: &[BinOp]) -> bool {
    matches!(inst, Inst::BinOp { op, .. } if ops.contains(op))
}

fn udiv(_: &Module, inst: &Inst) -> bool {
    binop_is(inst, &[BinOp::UDiv])
}

fn urem(_: &Module, inst: &Inst) -> bool {
    binop_is(inst, &[BinOp::URem])
}

fn sdiv(_: &Module, inst: &Inst) -> bool {
    binop_is(inst, &[BinOp::SDiv])
}

fn srem(_: &Module, inst: &Inst) -> bool {
    binop_is(inst, &[BinOp::SRem])
}

fn shift(_: &Module, inst: &Inst) -> bool {
    binop_is(inst, &[BinOp::Shl, BinOp::LShr, BinOp::AShr])
}

// ---------------------------------------------------------------------------
// Class names (entries of FSYM_TRUST_IR_UB_CLASSES)
// ---------------------------------------------------------------------------

pub const CLASS_CHAR_VALIDITY: &str = "Unicode scalar validity";
/// This conditional claim applies ONLY after whole-function admission.
/// Oracle attribution confirms the actual named scope refusal, not a skip.
pub const CHAR_BINDINGS_REFUSED: &str = "the function-scope admission gate refuses every entry parameter carrying Char by value and every direct Char block parameter or instruction result, including dead bindings, and refuses unresolved result typing before scanning; forged Char payloads under Char-free entry declarations are TypeError before Unicode checking";
/// Conservative source call-graph raisers: even bind_results([]) is retained.
pub const CHAR_BINDING_RAISERS: &[&str] = &[
    "<entry>",
    "Alloca",
    "ArraySplat",
    "AtomicLoad",
    "AtomicRMW",
    "AtomicStore",
    "BinOp",
    "BindSlot",
    "Borrow",
    "BorrowMut",
    "Call",
    "CallIndirect",
    "Cast",
    "CloseFrame",
    "CmpXchg",
    "Const",
    "Copy",
    "Dealloc",
    "DialectOp",
    "EndBorrow",
    "ExtractElement",
    "ExtractField",
    "FCmp",
    "Fence",
    "GEP",
    "GlobalAddr",
    "HeapAlloc",
    "ICmp",
    "InsertElement",
    "InsertField",
    "Invoke",
    "IsUnique",
    "Load",
    "LoadSlot",
    "MakeAggregate",
    "MemCopy",
    "MemSet",
    "NullPtr",
    "OpenFrame",
    "Overflow",
    "PtrData",
    "PtrFromParts",
    "PtrMetadata",
    "Release",
    "Retain",
    "Select",
    "SeqMap",
    "SeqMapAddK",
    "SeqMapNot",
    "Store",
    "UnOp",
    "Undef",
    RAISER_WALK,
];

pub const CLASS_NULL: &str = "null dereference";
pub const CLASS_BOUNDS: &str = "out of bounds / no provenance";
pub const CLASS_LANES: &str = "aggregate lanes and vector elements";
pub const CLASS_UAF: &str = "use after free / double free";
pub const CLASS_INVALID_FREE: &str = "invalid free";
pub const CLASS_MISALIGNED: &str = "misaligned access";
pub const CLASS_UNINIT: &str = "uninitialized read and poison inspection";
pub const CLASS_OVERLAP: &str = "memcpy overlap";
pub const CLASS_INTEGER: &str = "integer arithmetic";
pub const CLASS_FLOAT_TO_INT: &str = "float-to-integer conversion";
pub const CLASS_ALLOCATION: &str = "allocation size and placement";
pub const CLASS_POINTER: &str = "pointer arithmetic and address exposure";
pub const CLASS_UNREACHABLE: &str = "reaching unreachable";
pub const CLASS_CALLS: &str = "unsummarized call effects";
pub const CLASS_TENSOR: &str = "tensor contraction shapes";
const CLASS_TENSOR_REGION: &str = "tensor map/reduce/view shapes and indices";
const CLASS_TENSOR_COORDINATES: &str = "tensor gather/scatter coordinates and extents";
pub const CLASS_REFUSED: &str =
    "undef, ARC, binding frames, dialect ops, indirect calls, SeqMap, unwinding, coroutines";
pub const CLASS_HOST: &str = "host runtime handles and host models";

// ---------------------------------------------------------------------------
// Shared raiser groups and reasons
// ---------------------------------------------------------------------------

const SCALAR_ACCESSES: &[&str] = &[
    "Load",
    "Store",
    "AtomicLoad",
    "AtomicStore",
    "AtomicRMW",
    "CmpXchg",
];
const ACCESSES: &[&str] = &[
    "Load",
    "Store",
    "AtomicLoad",
    "AtomicStore",
    "AtomicRMW",
    "CmpXchg",
    "MemCopy",
    "MemSet",
];
const STORES: &[&str] = &["Store", "AtomicStore", "AtomicRMW", "CmpXchg"];
const GLOBAL_MATERIALIZERS: &[&str] = &["Const", "GlobalAddr"];
const ALLOCATORS: &[&str] = &["Alloca", "HeapAlloc"];
const REFUSED_MEMORY: &[&str] = &["CoroSuspend", "SeqMap"];

const GLOBAL_INIT_WRITE: &str = "materializing a module global writes its initializer's image exactly once, into the fresh allocation just placed for it, at its base, at the allocation's own placement alignment and exactly its size: never freed, never misaligned, never out of range";
const NOT_A_MATERIALIZER: &str = "a `Const` addressing no symbol materializes no global";
const INTEGER_SWITCH: &str =
    "fsym admits only `Constant::Int` switch cases, which materialize no global";
/// Why a placement (`Alloca`, `HeapAlloc`) cannot raise a `checked_access`
/// site, which the source call graph reaches from it only through a merged
/// name.
const PLACEMENT_BUILDS_ITS_IMAGE: &str = "a placement builds its fresh allocation's image with the byte-image constructor `Image::fill` (the heap slack tail), which the source call graph merges by name with `MemoryState::fill`, the MemSet store that reaches `checked_access` through `write_image`: the allocation is created, never accessed through a pointer";
const RECORDS_NEVER_REMOVED: &str = "the interpreter never removes an allocation record (a free marks it dead), so a pointer's allocation always resolves";
/// Why an instruction taking a pointer operand from the program can raise an
/// `unknown allocation` site only outside the run model.
pub const FORGED_ENTRY_POINTER: &str = "only an entry argument the embedder forged names an allocation the run never made (`InterpretPointer` is public and `execute_function` accepts it): a run starts from fresh memory, so an entry argument names no allocation, and the interpreter never removes an allocation record, so no pointer the run makes names an unknown one. Outside the run model; fsym's claims do not cover it (and exposing a parameter's address is an Unknown anyway)";
const ID_OVERFLOW: &str =
    "needs 2^64 allocations in one run; the interpreter's fuel bounds a run far below that";
const BINOP_ONLY_OVERFLOW: &str =
    "`Overflow` evaluates only Add/Sub/Mul through eval_int_binop: no division or shift";
const BINOP_ONLY_RMW: &str = "`AtomicRMW` evaluates only Add/Sub/And/Or/Xor (and compares) through eval_int_binop: no division or shift";
const HOST_MODEL: &str = "raised by a host model (the pinned RC runtime, handle-minting hosts) serving a body-less function: a call handing it a pointer or handle is an UnsummarizedCall Unknown, and a body-less entry is not scanned";
const ENTRY_HANDLE: &str = "a forged runtime handle in the harness's entry arguments: an embedder error, not UB of the function body (fsym leaves handle-typed values unmodeled)";
/// trust-ir v49: why no unwritten aggregate lane exists in a scanned run.
const NO_UNWRITTEN_LANE: &str = "a trust-ir v49 unwritten aggregate lane exists in a run only where an `Inst::Const` materializes a `Constant::Uninit` (no instruction yields one otherwise, and memory records one only when a value carrying one is stored) or where an entry argument carries one: fsym scans no function of a module that spells a `Constant::Uninit` anywhere (`module_unwritten_lane`), and an entry argument carrying one is outside the run model";
/// trust-ir v56 (amendment D Part 2, `SPEC_RATIFICATIONS` §21 rule 3): why a
/// failed `Assert` cannot raise the sites its exception object reaches.
const UNWIND_RAISE_ONLY: &str = "a failed check allocates its exception object (`raise_exception`: a fresh one-byte allocation, dead from birth) and takes its address only under `PanicStrategy::Unwind`, which `FsymRunModel::breach` places outside the run model; under the `Abort` default a failed check is the terminal panic and allocates nothing";
/// trust-ir v56: why an admitted `LandingPad` binds no value in a scanned run.
const PAD_BINDS_ONLY_UNDER_UNWIND: &str = "a landing pad binds its exception and selector only when an unwind edge entered it under `PanicStrategy::Unwind` (outside the run model, `FsymRunModel::breach`); under the `Abort` default the interpreter refuses a pad, and fsym refuses every invoke-family terminator (`Invoke`, `AssertInvoke`, `DropInvoke`, `InvokeIndirect`), so no admitted function enters one";
/// trust-ir v55 / v56 (amendment D): the drop and unwinding instructions the
/// interpreter now executes (a drop resolves to a call of its glue; `Resume`
/// re-raises under `Unwind`), every one refused at admission.
const REFUSED_DROPS_AND_UNWIND_TWINS: &[&str] = &["Drop", "DropInvoke", "InvokeIndirect", "Resume"];
/// trust-ir v55 (amendment D): a resolved drop runs its glue as a call.
const REFUSED_DROPS: &[&str] = &["Drop", "DropInvoke"];
/// trust-ir v49: an entry argument carrying an unwritten lane.
const ENTRY_UNWRITTEN_LANE: &str = "an unwritten aggregate lane in the harness's entry arguments: outside the run model (`FsymRunModel::breach`), where fsym's claims are not made";

const fn owed(
    by: &'static [&'static str],
    kind: FsymTrustIrDiagnosticKind,
    applies: fn(&Module, &Inst) -> bool,
    otherwise: &'static str,
) -> FsymUbRaise {
    FsymUbRaise {
        by,
        stance: FsymUbStance::Owed {
            kind,
            applies,
            otherwise,
        },
    }
}

const fn owed_always(by: &'static [&'static str], kind: FsymTrustIrDiagnosticKind) -> FsymUbRaise {
    owed(by, kind, always, "")
}

const fn refused(by: &'static [&'static str]) -> FsymUbRaise {
    FsymUbRaise {
        by,
        stance: FsymUbStance::Refused,
    }
}

const fn not_raised(by: &'static [&'static str], detail: &'static str) -> FsymUbRaise {
    FsymUbRaise {
        by,
        stance: FsymUbStance::NotRaised(detail),
    }
}

const fn outside(by: &'static [&'static str], detail: &'static str) -> FsymUbRaise {
    FsymUbRaise {
        by,
        stance: FsymUbStance::Outside(detail),
    }
}

const fn site(
    function: &'static str,
    message: &'static str,
    class: &'static str,
    raisers: &'static [FsymUbRaise],
) -> FsymInterpreterUbSite {
    FsymInterpreterUbSite {
        function,
        message,
        class,
        raisers,
    }
}

use FsymTrustIrDiagnosticKind as K;

/// Every `UndefinedBehavior` the reference interpreter at the pinned trust-ir
/// revision can raise (its non-test code), plus the
/// [`CALLEE_BODY`] pseudo-site for a callee's execution.
pub const FSYM_INTERPRETER_UB_SITES: &[FsymInterpreterUbSite] = &[
    site(
        "check_char_validity",
        "`char` value {:#x} is not a Unicode scalar value (",
        CLASS_CHAR_VALIDITY,
        &[
            not_raised(CHAR_BINDING_RAISERS, CHAR_BINDINGS_REFUSED),
            // Flat construction excludes Char captures; every Char SSA binding
            // is separately refused by validate_char_binding_scope.
            not_raised(&["MakeClosure"], CHAR_BINDINGS_REFUSED),
            // v56: a pad binds values only when entered under `Unwind`.
            not_raised(&["LandingPad"], PAD_BINDS_ONLY_UNDER_UNWIND),
            // v55 / v56: a resolved drop binds its glue's returns, the unwinding
            // indirect call its callee's; each is refused at admission.
            refused(&[
                "Drop",
                "DropInvoke",
                "InvokeIndirect",
                "TensorContract",
                "TensorMap",
                "TensorReduce",
                "TensorView",
                // Both new operations reach the same bind_results check;
                // neither has an admitted bounded tensor model.
                "TensorGather",
                "TensorScatter",
            ]),
        ],
    ),
    // Host models and the harness.
    site(
        "resolve",
        "handle of runtime {} passed to {} (minted as {}, e",
        CLASS_HOST,
        &[
            // v55: a resolved drop calls its glue, which may be host-served.
            refused(REFUSED_DROPS),
        ],
    ),
    site(
        "resolve",
        "handle of runtime {} minted by host model {} passe",
        CLASS_HOST,
        &[
            // v55: a resolved drop calls its glue, which may be host-served.
            refused(REFUSED_DROPS),
        ],
    ),
    site(
        "recorded",
        "handle #{id} ({value_ty}) was never minted in this",
        CLASS_HOST,
        &[
            outside(&[RAISER_ENTRY], HOST_MODEL),
            // v55: a resolved drop's glue may be host-served.
            refused(REFUSED_DROPS),
        ],
    ),
    site(
        "recorded",
        "handle #{id} is typed {value_ty} but was minted as",
        CLASS_HOST,
        &[
            outside(&[RAISER_ENTRY], HOST_MODEL),
            // v55: a resolved drop's glue may be host-served.
            refused(REFUSED_DROPS),
        ],
    ),
    site(
        "recorded",
        "handle #{id} of runtime {} used after release",
        CLASS_HOST,
        &[
            outside(&[RAISER_ENTRY], HOST_MODEL),
            // v55: a resolved drop's glue may be host-served.
            refused(REFUSED_DROPS),
        ],
    ),
    site(
        "execute_function",
        "entry argument carries {what}, which was never min",
        CLASS_HOST,
        &[outside(&[RAISER_ENTRY], ENTRY_HANDLE)],
    ),
    site(
        "execute_host_rc_op",
        "@{name}: null object pointer",
        CLASS_HOST,
        &[outside(&[RAISER_ENTRY], HOST_MODEL)],
    ),
    // Control flow.
    site(
        "execute_node",
        "executed unreachable",
        CLASS_UNREACHABLE,
        &[owed_always(&["Unreachable"], K::UnreachableReached)],
    ),
    // v56 (amendment D Part 2, §21 rule 6): under `Unwind`, `Resume` of a
    // value that is no exception object a pad produced.
    site(
        "execute_node",
        "resume: the value is not an exception object a lan",
        CLASS_REFUSED,
        &[refused(&["Resume"])],
    ),
    // Binding frames.
    site(
        "execute_node",
        "OpenFrame: frame id overflow",
        CLASS_REFUSED,
        &[refused(&["OpenFrame"])],
    ),
    site(
        "execute_node",
        "BindSlot: slot {slot} out of range for frame of {}",
        CLASS_REFUSED,
        &[refused(&["BindSlot"])],
    ),
    site(
        "execute_node",
        "LoadSlot: slot {slot} out of range for frame of {}",
        CLASS_REFUSED,
        &[refused(&["LoadSlot"])],
    ),
    site(
        "execute_node",
        "CloseFrame: frame is not open (double close)",
        CLASS_REFUSED,
        &[refused(&["CloseFrame"])],
    ),
    site(
        "expect_open_frame",
        "{op}: frame is not open",
        CLASS_REFUSED,
        &[refused(&["BindSlot", "LoadSlot"])],
    ),
    site(
        "scalar_poison",
        "{what} of non-scalar type {ty} is not executable (",
        CLASS_REFUSED,
        &[refused(&["LoadSlot", "Undef"])],
    ),
    // v54 (amendment P): a failed sited check resolves its run-time location.
    // Only a site's `Value` location can be null or dangling; the admission
    // gate refuses every sited check (`unsupported_nonterminator_detail`,
    // and `AssertInvoke` as a terminator), so a scanned `Assert` is unsited.
    site(
        "resolve_panic_location",
        "assert: panic location is null or dangling",
        CLASS_REFUSED,
        &[
            not_raised(
                &["Assert"],
                "a scanned Assert carries no panic site: the admission gate refuses a sited check by name, and an unsited one resolves no location",
            ),
            refused(&["AssertInvoke"]),
        ],
    ),
    // Allocation.
    site(
        "eval_alloca",
        "Alloca: count must be positive",
        CLASS_ALLOCATION,
        &[
            owed(
                ALLOCATORS,
                K::Arithmetic,
                allocation_with_count,
                "a count-less allocation has count 1",
            ),
            refused(&["SeqMap"]),
        ],
    ),
    site(
        "eval_alloca",
        "Alloca: count {} does not fit u64",
        CLASS_ALLOCATION,
        &[
            owed(
                ALLOCATORS,
                K::Arithmetic,
                allocation_with_count,
                "a count-less allocation has count 1",
            ),
            refused(&["SeqMap"]),
        ],
    ),
    site(
        "eval_alloca",
        "Alloca: allocation size overflow",
        CLASS_ALLOCATION,
        &[
            owed(
                ALLOCATORS,
                K::Arithmetic,
                allocation_with_count,
                "a count-less allocation is one element of a type whose size fits u64",
            ),
            refused(&["SeqMap"]),
        ],
    ),
    site(
        "alloc_with_slack",
        "Alloca: allocation id overflow",
        CLASS_ALLOCATION,
        &[
            not_raised(ALLOCATORS, ID_OVERFLOW),
            not_raised(GLOBAL_MATERIALIZERS, ID_OVERFLOW),
            not_raised(&["Switch"], INTEGER_SWITCH),
            refused(&["SeqMap"]),
            // v56: a failed check's exception object, under `Unwind` only.
            not_raised(&["Assert"], UNWIND_RAISE_ONLY),
            refused(&["AssertInvoke"]),
        ],
    ),
    // Loads.
    site(
        "eval_load",
        "Load: reading uninitialized byte at offset {}",
        CLASS_UNINIT,
        &[
            owed_always(
                &["Load", "AtomicLoad", "AtomicRMW", "CmpXchg"],
                K::Uninitialized,
            ),
            refused(&["SeqMap"]),
        ],
    ),
    // trust-ir v49 unwritten aggregate lanes.
    site(
        "decode_image_with_unwritten_lanes",
        "Load: reading uninitialized byte at offset {} of a",
        CLASS_UNINIT,
        &[
            not_raised(
                &["Load", "AtomicLoad", "AtomicRMW", "CmpXchg"],
                NO_UNWRITTEN_LANE,
            ),
            refused(&["SeqMap"]),
        ],
    ),
    site(
        "encode_image",
        "encoding an unwritten lane (uninit) of type {} as ",
        CLASS_UNINIT,
        &[
            not_raised(STORES, NO_UNWRITTEN_LANE),
            not_raised(GLOBAL_MATERIALIZERS, NO_UNWRITTEN_LANE),
            not_raised(&["Switch"], NO_UNWRITTEN_LANE),
            refused(REFUSED_MEMORY),
        ],
    ),
    site(
        "eval_extract_field",
        "extract_field: field {field} of {} is an unwritten",
        CLASS_UNINIT,
        &[not_raised(&["ExtractField"], NO_UNWRITTEN_LANE)],
    ),
    site(
        "eval_store",
        "Store (atomic/volatile): the stored aggregate has ",
        CLASS_UNINIT,
        &[
            not_raised(STORES, NO_UNWRITTEN_LANE),
            refused(REFUSED_MEMORY),
        ],
    ),
    site(
        "reject_partial",
        "{op}: use of an unwritten aggregate lane (uninit) ",
        CLASS_UNINIT,
        &[
            refused(&[
                "TensorContract",
                "TensorMap",
                "TensorReduce",
                "TensorView",
                "TensorGather",
                "TensorScatter",
            ]),
            outside(&[RAISER_ENTRY], ENTRY_UNWRITTEN_LANE),
            not_raised(&["MakeClosure"], NO_UNWRITTEN_LANE),
            FsymUbRaise {
                by: &[
                    RAISER_WALK,
                    "Alloca",
                    "ArraySplat",
                    "Assert",
                    "Assume",
                    "AtomicLoad",
                    "AtomicRMW",
                    "AtomicStore",
                    "BinOp",
                    "BindSlot",
                    "Borrow",
                    "BorrowMut",
                    "Call",
                    "CallIndirect",
                    "Cast",
                    "CloseFrame",
                    "CmpXchg",
                    "CondBr",
                    "Const",
                    "CoroSuspend",
                    "Dealloc",
                    "DialectOp",
                    "ExtractElement",
                    "ExtractField",
                    "FCmp",
                    "GEP",
                    "GlobalAddr",
                    "HeapAlloc",
                    "ICmp",
                    "InsertElement",
                    "InsertField",
                    "Invoke",
                    "IsUnique",
                    "Load",
                    "LoadSlot",
                    "MakeAggregate",
                    "MemCopy",
                    "MemSet",
                    "Overflow",
                    "PtrData",
                    "PtrFromParts",
                    "PtrMetadata",
                    "Release",
                    "Retain",
                    "Select",
                    "SeqMap",
                    "Store",
                    "Switch",
                    "UnOp",
                ],
                stance: FsymUbStance::NotRaised(NO_UNWRITTEN_LANE),
            },
            // v54: a sited check with an unwind edge is refused at admission.
            refused(&["AssertInvoke"]),
            // v55 / v56: drops (now calls of their glue), the unwinding indirect
            // call and `Resume`, each refused at admission.
            refused(REFUSED_DROPS_AND_UNWIND_TWINS),
        ],
    ),
    // GEP.
    site(
        "eval_gep",
        "GEP: negative index {}",
        CLASS_POINTER,
        &[
            owed_always(&["GEP"], K::PointerArithmetic),
            refused(&["CoroSuspend"]),
        ],
    ),
    site(
        "eval_gep",
        "GEP: index {} does not fit u64",
        CLASS_POINTER,
        &[
            owed_always(&["GEP"], K::PointerArithmetic),
            refused(&["CoroSuspend"]),
        ],
    ),
    site(
        "eval_gep",
        "GEP: byte offset overflow",
        CLASS_POINTER,
        &[
            owed_always(&["GEP"], K::PointerArithmetic),
            refused(&["CoroSuspend"]),
        ],
    ),
    site(
        "eval_gep",
        "GEP: pointer offset overflow",
        CLASS_POINTER,
        &[
            owed_always(&["GEP"], K::PointerArithmetic),
            refused(&["CoroSuspend"]),
        ],
    ),
    // Bulk memory.
    site(
        "eval_mem_copy",
        "MemCopy: source [{}..{}) and destination [{}..{}) ",
        CLASS_OVERLAP,
        &[owed(
            &["MemCopy"],
            K::Overlap,
            memcpy_semantics,
            "with `overlap` (memmove semantics) overlapping ranges are defined",
        )],
    ),
    site(
        "bulk_byte_count",
        "{op}: byte count {} exceeds u64",
        CLASS_BOUNDS,
        &[owed_always(&["MemCopy", "MemSet"], K::OutOfBounds)],
    ),
    // Casts.
    site(
        "eval_cast",
        "{op}: NaN cannot be converted to integer",
        CLASS_FLOAT_TO_INT,
        &[
            refused(&["TensorMap"]),
            owed(
                &["Cast"],
                K::Arithmetic,
                raw_float_to_int,
                "only the raw float-to-integer casts (FPToSI / FPToUI) raise it",
            ),
        ],
    ),
    site(
        "eval_cast",
        "{op}: {value} out of range for {dst_ty}",
        CLASS_FLOAT_TO_INT,
        &[
            refused(&["TensorMap"]),
            owed(
                &["Cast"],
                K::Arithmetic,
                raw_float_to_int,
                "only the raw float-to-integer casts (FPToSI / FPToUI) raise it",
            ),
        ],
    ),
    site(
        "eval_cast",
        "{op}: address {} does not fit u64",
        CLASS_POINTER,
        &[
            refused(&["TensorMap"]),
            owed(
                &["Cast"],
                K::PointerArithmetic,
                pointer_integer_cast,
                "only an integer-to-pointer cast names an address",
            ),
        ],
    ),
    site(
        "eval_bitcast",
        "Bitcast: address {} does not fit u64",
        CLASS_POINTER,
        &[
            refused(&["TensorMap"]),
            owed(
                &["Cast"],
                K::PointerArithmetic,
                pointer_integer_cast,
                "only an integer-to-pointer bitcast / transmute names an address",
            ),
        ],
    ),
    // Aggregate lanes and vector elements.
    site(
        "check_enum_payload_lane",
        "enum {enum_ty}: lane {field} belongs to no field o",
        CLASS_LANES,
        &[owed_always(
            &["ExtractField", "InsertField"],
            K::OutOfBounds,
        )],
    ),
    site(
        "eval_extract_field",
        "field {field} is out of bounds for {}",
        CLASS_LANES,
        &[owed_always(&["ExtractField"], K::OutOfBounds)],
    ),
    site(
        "eval_insert_field",
        "insert_field cannot rewrite an enum discriminant (",
        CLASS_LANES,
        &[owed_always(&["InsertField"], K::OutOfBounds)],
    ),
    site(
        "eval_insert_field",
        "field {field} is out of bounds for {}",
        CLASS_LANES,
        &[owed_always(&["InsertField"], K::OutOfBounds)],
    ),
    site(
        "eval_extract_element",
        "element {index} is out of bounds for {}",
        CLASS_LANES,
        &[owed_always(&["ExtractElement"], K::OutOfBounds)],
    ),
    site(
        "eval_insert_element",
        "element {index} is out of bounds for {}",
        CLASS_LANES,
        &[owed_always(&["InsertElement"], K::OutOfBounds)],
    ),
    site(
        "runtime_index",
        "negative element index {}",
        CLASS_LANES,
        &[owed_always(
            &["ExtractElement", "InsertElement"],
            K::OutOfBounds,
        )],
    ),
    site(
        "runtime_index",
        "element index {} does not fit usize",
        CLASS_LANES,
        &[owed_always(
            &["ExtractElement", "InsertElement"],
            K::OutOfBounds,
        )],
    ),
    // ARC (and the RC host model).
    site(
        "check_rc_cell",
        "@{entry}: pointer does not reference a known alloc",
        CLASS_HOST,
        &[outside(&[RAISER_ENTRY], HOST_MODEL)],
    ),
    site(
        "check_rc_cell",
        "@{entry}: pointer references a freed allocation",
        CLASS_HOST,
        &[outside(&[RAISER_ENTRY], HOST_MODEL)],
    ),
    site(
        "check_rc_cell",
        "@{entry}: pointer addresses {actual}, not a cell o",
        CLASS_HOST,
        &[outside(&[RAISER_ENTRY], HOST_MODEL)],
    ),
    site(
        "check_rc_cell",
        "@{entry}: pointer is at offset {} of its allocatio",
        CLASS_HOST,
        &[outside(&[RAISER_ENTRY], HOST_MODEL)],
    ),
    site(
        "retain",
        "Retain: reference count overflow",
        CLASS_REFUSED,
        &[refused(&["Retain"]), outside(&[RAISER_ENTRY], HOST_MODEL)],
    ),
    site(
        "release",
        "Release: reference count underflow (double free)",
        CLASS_REFUSED,
        &[refused(&["Release"]), outside(&[RAISER_ENTRY], HOST_MODEL)],
    ),
    site(
        "is_unique",
        "IsUnique: pointer does not reference a known alloc",
        CLASS_REFUSED,
        &[refused(&["IsUnique"]), outside(&[RAISER_ENTRY], HOST_MODEL)],
    ),
    site(
        "is_unique",
        "IsUnique: pointer references a freed allocation",
        CLASS_REFUSED,
        &[refused(&["IsUnique"]), outside(&[RAISER_ENTRY], HOST_MODEL)],
    ),
    site(
        "arc_allocation_mut",
        "{op}: pointer does not reference a known allocatio",
        CLASS_REFUSED,
        &[
            refused(&["Retain", "Release"]),
            outside(&[RAISER_ENTRY], HOST_MODEL),
        ],
    ),
    site(
        "arc_allocation_mut",
        "{op}: pointer references a freed allocation",
        CLASS_REFUSED,
        &[
            refused(&["Retain", "Release"]),
            outside(&[RAISER_ENTRY], HOST_MODEL),
        ],
    ),
    // trust-ir `25624afd`: the ARC trio counts only a reference-counted cell
    // (`HeapAlloc { SwiftHeap | CleanHeap }`); on a stack, global,
    // `RustHeap` or `CMalloc` allocation each is undefined behaviour, as
    // Lean's `requireArcRef` decides. fsym refuses the three at admission.
    site(
        "is_unique",
        "IsUnique: pointer addresses {actual}, not a refere",
        CLASS_REFUSED,
        &[refused(&["IsUnique"]), outside(&[RAISER_ENTRY], HOST_MODEL)],
    ),
    site(
        "is_unique",
        "IsUnique: pointer is at offset {} of its cell, not",
        CLASS_REFUSED,
        &[refused(&["IsUnique"]), outside(&[RAISER_ENTRY], HOST_MODEL)],
    ),
    site(
        "arc_allocation_mut",
        "{op}: pointer addresses {actual}, not a reference-",
        CLASS_REFUSED,
        &[
            refused(&["Retain", "Release"]),
            outside(&[RAISER_ENTRY], HOST_MODEL),
        ],
    ),
    site(
        "arc_allocation_mut",
        "{op}: pointer is at offset {} of its cell, not at ",
        CLASS_REFUSED,
        &[
            refused(&["Retain", "Release"]),
            outside(&[RAISER_ENTRY], HOST_MODEL),
        ],
    ),
    // Deallocation.
    site(
        "dealloc",
        "Dealloc: pointer must reference allocation base",
        CLASS_INVALID_FREE,
        &[owed_always(&["Dealloc"], K::InvalidFree)],
    ),
    site(
        "dealloc",
        "Dealloc: unknown allocation {}",
        CLASS_INVALID_FREE,
        &[owed_always(&["Dealloc"], K::InvalidFree)],
    ),
    site(
        "dealloc",
        "Dealloc: allocation is already dead",
        CLASS_UAF,
        &[owed_always(&["Dealloc"], K::UseAfterFree)],
    ),
    // trust-ir `bf7ee706`: a reference-counted (`SwiftHeap` / `CleanHeap`)
    // cell is released by `Release`, never by `Dealloc`. fsym's InvalidFree
    // verdict decides it from the freed object's allocation origin.
    site(
        "dealloc",
        "Dealloc of a {origin:?} cell: a reference-counted ",
        CLASS_INVALID_FREE,
        &[owed_always(&["Dealloc"], K::InvalidFree)],
    ),
    // trust-ir `c06a487f`: freeing an allocation under a live borrow (a thin
    // `Borrow` / `BorrowMut` of an address inside its requested bytes not yet
    // ended by an `EndBorrow`) is undefined behaviour, as Lean's `semDealloc`
    // refuses a borrowed permission. fsym does not track borrow counts: its
    // InvalidFree verdict at a `Dealloc` is never `Safe` on a path that
    // borrowed, nor for an object a call on the path could reach (the callee
    // may have left a borrow of it live).
    site(
        "dealloc",
        "Dealloc: allocation is under a live borrow ({} Bor",
        CLASS_INVALID_FREE,
        &[owed_always(&["Dealloc"], K::InvalidFree)],
    ),
    // Addresses.
    site(
        "address",
        "{op}: unknown allocation {}",
        CLASS_BOUNDS,
        &[
            refused(&["TensorMap"]),
            outside(&["Cast", "GEP", "ICmp"], FORGED_ENTRY_POINTER),
            outside(STORES, FORGED_ENTRY_POINTER),
            not_raised(GLOBAL_MATERIALIZERS, RECORDS_NEVER_REMOVED),
            not_raised(&["Switch"], INTEGER_SWITCH),
            refused(REFUSED_MEMORY),
            // v56: a failed check's exception object, under `Unwind` only.
            not_raised(&["Assert"], UNWIND_RAISE_ONLY),
            refused(&["AssertInvoke", "Resume"]),
        ],
    ),
    site(
        "address",
        "{op}: pointer address overflow",
        CLASS_POINTER,
        &[
            refused(&["TensorMap"]),
            owed(
                &["ICmp"],
                K::PointerArithmetic,
                pointer_comparison,
                "only a pointer comparison materializes operand addresses",
            ),
            owed(
                &["Cast"],
                K::PointerArithmetic,
                pointer_integer_cast,
                "only a pointer-to-integer cast materializes an address",
            ),
            owed_always(&["GEP"], K::PointerArithmetic),
            owed(
                STORES,
                K::PointerArithmetic,
                stores_address,
                "a value with no pointer lane encodes no address",
            ),
            owed(
                GLOBAL_MATERIALIZERS,
                K::PointerArithmetic,
                global_materializer,
                NOT_A_MATERIALIZER,
            ),
            not_raised(&["Switch"], INTEGER_SWITCH),
            refused(REFUSED_MEMORY),
            // v56: a failed check's exception object, under `Unwind` only.
            not_raised(&["Assert"], UNWIND_RAISE_ONLY),
            refused(&["AssertInvoke", "Resume"]),
        ],
    ),
    site(
        "check_address",
        "{op}: address {address:#x} is outside the target's",
        CLASS_POINTER,
        &[
            refused(&["TensorMap"]),
            owed(
                &["ICmp"],
                K::PointerArithmetic,
                pointer_comparison,
                "only a pointer comparison materializes operand addresses",
            ),
            owed(
                &["Cast"],
                K::PointerArithmetic,
                pointer_integer_cast,
                "only an integer-to-pointer cast names an address",
            ),
            owed_always(&["GEP"], K::PointerArithmetic),
            owed(
                STORES,
                K::PointerArithmetic,
                stores_address,
                "a value with no pointer lane encodes no address",
            ),
            owed(
                GLOBAL_MATERIALIZERS,
                K::PointerArithmetic,
                global_materializer,
                NOT_A_MATERIALIZER,
            ),
            not_raised(&["Switch"], INTEGER_SWITCH),
            refused(REFUSED_MEMORY),
        ],
    ),
    // Accesses.
    site(
        "checked_access",
        "{op}: unknown allocation {}",
        CLASS_BOUNDS,
        &[
            outside(ACCESSES, FORGED_ENTRY_POINTER),
            not_raised(GLOBAL_MATERIALIZERS, RECORDS_NEVER_REMOVED),
            not_raised(ALLOCATORS, PLACEMENT_BUILDS_ITS_IMAGE),
            not_raised(&["Switch"], INTEGER_SWITCH),
            refused(REFUSED_MEMORY),
            // v56: a failed check's exception object, under `Unwind` only.
            not_raised(&["Assert"], UNWIND_RAISE_ONLY),
            refused(&["AssertInvoke"]),
        ],
    ),
    site(
        "checked_access",
        "{op}: use after dealloc",
        CLASS_UAF,
        &[
            owed_always(ACCESSES, K::UseAfterFree),
            not_raised(GLOBAL_MATERIALIZERS, GLOBAL_INIT_WRITE),
            not_raised(ALLOCATORS, PLACEMENT_BUILDS_ITS_IMAGE),
            not_raised(&["Switch"], INTEGER_SWITCH),
            refused(REFUSED_MEMORY),
            // v56: a failed check's exception object, under `Unwind` only.
            not_raised(&["Assert"], UNWIND_RAISE_ONLY),
            refused(&["AssertInvoke"]),
        ],
    ),
    site(
        "checked_access",
        "{op}: pointer address overflow",
        CLASS_BOUNDS,
        &[
            owed_always(ACCESSES, K::OutOfBounds),
            not_raised(GLOBAL_MATERIALIZERS, GLOBAL_INIT_WRITE),
            not_raised(ALLOCATORS, PLACEMENT_BUILDS_ITS_IMAGE),
            not_raised(&["Switch"], INTEGER_SWITCH),
            refused(REFUSED_MEMORY),
            // v56: a failed check's exception object, under `Unwind` only.
            not_raised(&["Assert"], UNWIND_RAISE_ONLY),
            refused(&["AssertInvoke"]),
        ],
    ),
    site(
        "checked_access",
        "{op}: pointer address {address} is not aligned to ",
        CLASS_MISALIGNED,
        &[
            owed_always(SCALAR_ACCESSES, K::Misaligned),
            not_raised(
                &["MemCopy", "MemSet"],
                "bulk accesses are byte-granular (checked at alignment 1)",
            ),
            not_raised(GLOBAL_MATERIALIZERS, GLOBAL_INIT_WRITE),
            not_raised(ALLOCATORS, PLACEMENT_BUILDS_ITS_IMAGE),
            not_raised(&["Switch"], INTEGER_SWITCH),
            refused(REFUSED_MEMORY),
            // v56: a failed check's exception object, under `Unwind` only.
            not_raised(&["Assert"], UNWIND_RAISE_ONLY),
            refused(&["AssertInvoke"]),
        ],
    ),
    site(
        "checked_access",
        "{op}: access range overflow",
        CLASS_BOUNDS,
        &[
            owed_always(ACCESSES, K::OutOfBounds),
            not_raised(GLOBAL_MATERIALIZERS, GLOBAL_INIT_WRITE),
            not_raised(ALLOCATORS, PLACEMENT_BUILDS_ITS_IMAGE),
            not_raised(&["Switch"], INTEGER_SWITCH),
            refused(REFUSED_MEMORY),
            // v56: a failed check's exception object, under `Unwind` only.
            not_raised(&["Assert"], UNWIND_RAISE_ONLY),
            refused(&["AssertInvoke"]),
        ],
    ),
    site(
        "checked_access",
        "{op}: access [{}..{}) is out of bounds for allocat",
        CLASS_BOUNDS,
        &[
            owed_always(ACCESSES, K::OutOfBounds),
            not_raised(GLOBAL_MATERIALIZERS, GLOBAL_INIT_WRITE),
            not_raised(ALLOCATORS, PLACEMENT_BUILDS_ITS_IMAGE),
            not_raised(&["Switch"], INTEGER_SWITCH),
            refused(REFUSED_MEMORY),
            // v56: a failed check's exception object, under `Unwind` only.
            not_raised(&["Assert"], UNWIND_RAISE_ONLY),
            refused(&["AssertInvoke"]),
        ],
    ),
    site(
        "expect_pointer",
        "{op}: null pointer dereference",
        CLASS_NULL,
        &[
            owed_always(ACCESSES, K::NullDeref),
            owed_always(&["GEP", "Borrow", "BorrowMut"], K::NullDeref),
            owed_always(&["Dealloc"], K::InvalidFree),
            refused(&["Retain", "Release", "IsUnique", "CoroSuspend", "SeqMap"]),
        ],
    ),
    site(
        "expect_pointer",
        "{op}: pointer value {addr} has no allocation prove",
        CLASS_BOUNDS,
        &[
            owed_always(ACCESSES, K::OutOfBounds),
            owed_always(&["Borrow", "BorrowMut"], K::OutOfBounds),
            owed_always(&["Dealloc"], K::InvalidFree),
            not_raised(
                &["GEP"],
                "eval_gep handles a no-provenance base before expect_pointer (GEP on one is defined)",
            ),
            refused(&["Retain", "Release", "IsUnique", "CoroSuspend", "SeqMap"]),
        ],
    ),
    // Integer arithmetic.
    site(
        "eval_int_binop",
        "unsigned division by zero",
        CLASS_INTEGER,
        &[
            refused(&["TensorContract", "TensorMap", "TensorReduce"]),
            owed(
                &["BinOp"],
                K::Arithmetic,
                udiv,
                "only UDiv divides unsigned",
            ),
            not_raised(&["Overflow"], BINOP_ONLY_OVERFLOW),
            not_raised(&["AtomicRMW"], BINOP_ONLY_RMW),
        ],
    ),
    site(
        "eval_int_binop",
        "unsigned remainder by zero",
        CLASS_INTEGER,
        &[
            refused(&["TensorContract", "TensorMap", "TensorReduce"]),
            owed(&["BinOp"], K::Arithmetic, urem, "only URem"),
            not_raised(&["Overflow"], BINOP_ONLY_OVERFLOW),
            not_raised(&["AtomicRMW"], BINOP_ONLY_RMW),
        ],
    ),
    site(
        "eval_int_binop",
        "signed division by zero",
        CLASS_INTEGER,
        &[
            refused(&["TensorContract", "TensorMap", "TensorReduce"]),
            owed(&["BinOp"], K::Arithmetic, sdiv, "only SDiv"),
            not_raised(&["Overflow"], BINOP_ONLY_OVERFLOW),
            not_raised(&["AtomicRMW"], BINOP_ONLY_RMW),
        ],
    ),
    site(
        "eval_int_binop",
        "signed division overflow",
        CLASS_INTEGER,
        &[
            refused(&["TensorContract", "TensorMap", "TensorReduce"]),
            owed(&["BinOp"], K::Arithmetic, sdiv, "only SDiv"),
            not_raised(&["Overflow"], BINOP_ONLY_OVERFLOW),
            not_raised(&["AtomicRMW"], BINOP_ONLY_RMW),
        ],
    ),
    site(
        "eval_int_binop",
        "signed remainder by zero",
        CLASS_INTEGER,
        &[
            refused(&["TensorContract", "TensorMap", "TensorReduce"]),
            owed(&["BinOp"], K::Arithmetic, srem, "only SRem"),
            not_raised(&["Overflow"], BINOP_ONLY_OVERFLOW),
            not_raised(&["AtomicRMW"], BINOP_ONLY_RMW),
        ],
    ),
    site(
        "eval_int_binop",
        "signed remainder overflow",
        CLASS_INTEGER,
        &[
            refused(&["TensorContract", "TensorMap", "TensorReduce"]),
            owed(&["BinOp"], K::Arithmetic, srem, "only SRem"),
            not_raised(&["Overflow"], BINOP_ONLY_OVERFLOW),
            not_raised(&["AtomicRMW"], BINOP_ONLY_RMW),
        ],
    ),
    site(
        "shift_amount",
        "shift amount {} is out of range for {bits}-bit int",
        CLASS_INTEGER,
        &[
            refused(&["TensorContract", "TensorMap", "TensorReduce"]),
            owed(&["BinOp"], K::Arithmetic, shift, "only Shl / LShr / AShr"),
            not_raised(&["Overflow"], BINOP_ONLY_OVERFLOW),
            not_raised(&["AtomicRMW"], BINOP_ONLY_RMW),
        ],
    ),
    // Poison inspection.
    site(
        "eval_tensor_contract",
        "tensor contraction: paired axes have different ext",
        CLASS_TENSOR,
        &[refused(&["TensorContract"])],
    ),
    site(
        "eval_tensor_contract",
        "tensor contraction: the result has more elements t",
        CLASS_TENSOR,
        &[refused(&["TensorContract"])],
    ),
    site(
        "eval_tensor_map",
        "tensor map: operand extents differ",
        CLASS_TENSOR_REGION,
        &[refused(&["TensorMap"])],
    ),
    site(
        "eval_tensor_reduce",
        "tensor reduction: the result has more elements tha",
        CLASS_TENSOR_REGION,
        &[refused(&["TensorReduce"])],
    ),
    site(
        "view_value",
        "tensor view: an index expression overflows",
        CLASS_TENSOR_REGION,
        &[refused(&["TensorView"])],
    ),
    site(
        "view_node",
        "tensor view: an index expression divides by zero",
        CLASS_TENSOR_REGION,
        &[refused(&["TensorView"])],
    ),
    site(
        "eval_tensor_view",
        "tensor view: a result extent does not fit usize",
        CLASS_TENSOR_REGION,
        &[refused(&["TensorView"])],
    ),
    site(
        "eval_tensor_view",
        "tensor view: the result has more elements than usi",
        CLASS_TENSOR_REGION,
        &[refused(&["TensorView"])],
    ),
    site(
        "eval_tensor_view",
        "tensor view: a source coordinate is out of range",
        CLASS_TENSOR_REGION,
        &[refused(&["TensorView"])],
    ),
    // trust-ir v69 gather/scatter (`interpret/tensor_gather_scatter.rs`): each
    // instruction is refused at admission.
    site(
        "eval_tensor_gather",
        "tensor gather: coordinate tensors have different e",
        CLASS_TENSOR_COORDINATES,
        &[refused(&["TensorGather"])],
    ),
    site(
        "eval_tensor_gather",
        "tensor gather: a coordinate is outside its axis",
        CLASS_TENSOR_COORDINATES,
        &[refused(&["TensorGather"])],
    ),
    site(
        "eval_tensor_scatter",
        "tensor scatter: coordinate tensor extents differ f",
        CLASS_TENSOR_COORDINATES,
        &[refused(&["TensorScatter"])],
    ),
    site(
        "eval_tensor_scatter",
        "tensor scatter: a coordinate is outside its axis",
        CLASS_TENSOR_COORDINATES,
        &[refused(&["TensorScatter"])],
    ),
    site(
        "reject_partial_error",
        "{op}: use of an uninitialized value — poison (unin",
        CLASS_UNINIT,
        &[
            refused(&[
                "TensorContract",
                "TensorMap",
                "TensorReduce",
                "TensorView",
                "TensorGather",
                "TensorScatter",
            ]),
            FsymUbRaise {
                by: &["MakeClosure"],
                stance: FsymUbStance::AtSource {
                    kind: K::Uninitialized,
                    detail: "capture poison can only originate at a Load (which owes Uninitialized); Undef and unbound LoadSlot are refused, and unwritten/forged entry values are outside the run model",
                },
            },
            FsymUbRaise {
                by: &[
                    RAISER_ENTRY,
                    RAISER_WALK,
                    "Alloca",
                    "ArraySplat",
                    "Assert",
                    "Assume",
                    "AtomicLoad",
                    "AtomicRMW",
                    "AtomicStore",
                    "BinOp",
                    "BindSlot",
                    "Borrow",
                    "BorrowMut",
                    "Call",
                    "CallIndirect",
                    "Cast",
                    "CloseFrame",
                    "CmpXchg",
                    "CondBr",
                    "Const",
                    "CoroSuspend",
                    "Dealloc",
                    "DialectOp",
                    "ExtractElement",
                    "ExtractField",
                    "FCmp",
                    "GEP",
                    "GlobalAddr",
                    "HeapAlloc",
                    "ICmp",
                    "InsertElement",
                    "InsertField",
                    "Invoke",
                    "IsUnique",
                    "Load",
                    "LoadSlot",
                    "MakeAggregate",
                    "MemCopy",
                    "MemSet",
                    "Overflow",
                    "PtrData",
                    "PtrFromParts",
                    "PtrMetadata",
                    "Release",
                    "Retain",
                    "Select",
                    "SeqMap",
                    "Store",
                    "Switch",
                    "UnOp",
                ],
                stance: FsymUbStance::AtSource {
                    kind: K::Uninitialized,
                    detail: "poison is made only by a plain Load of uninitialized bytes (which owes an Uninitialized verdict), Undef and an unbound LoadSlot (refused); a MemCopy moves uninitialized bytes, which a later Load owes",
                },
            },
            // v54: a sited check with an unwind edge is refused at admission.
            refused(&["AssertInvoke"]),
            // v55 / v56: drops (now calls of their glue), the unwinding indirect
            // call and `Resume`, each refused at admission.
            refused(REFUSED_DROPS_AND_UNWIND_TWINS),
        ],
    ),
    // A callee's body.
    site(
        CALLEE_FUNCTION,
        CALLEE_BODY,
        CLASS_CALLS,
        &[
            owed(
                &["Call"],
                K::UnsummarizedCall,
                runs_a_callee,
                "a call to a bulk-memory symbol is checked as the MemSet / MemCopy access trust-cg-lower lowers it to (null, bounds, lifetime, overlap verdicts), not as a callee",
            ),
            refused(&["CallIndirect", "Invoke", "SeqMap"]),
            // v55 / v56 (amendment D): a resolved drop runs its glue's body as
            // a call; the unwinding indirect call runs its callee's. Each is
            // refused at admission.
            refused(&["Drop", "DropInvoke", "InvokeIndirect"]),
        ],
    ),
];

/// Every `trust_ir::Inst` variant's name. EXHAUSTIVE on purpose (no
/// wildcard): a variant added to trust-ir fails to compile here until it is
/// placed in the map.
pub fn fsym_inst_variant_name(inst: &Inst) -> &'static str {
    match inst {
        Inst::BinOp { .. } => "BinOp",
        Inst::UnOp { .. } => "UnOp",
        Inst::Overflow { .. } => "Overflow",
        Inst::ICmp { .. } => "ICmp",
        Inst::FCmp { .. } => "FCmp",
        Inst::Cast { .. } => "Cast",
        Inst::Load { .. } => "Load",
        Inst::Store { .. } => "Store",
        Inst::Alloca { .. } => "Alloca",
        Inst::HeapAlloc { .. } => "HeapAlloc",
        Inst::GEP { .. } => "GEP",
        Inst::PtrData { .. } => "PtrData",
        Inst::PtrMetadata { .. } => "PtrMetadata",
        Inst::PtrFromParts { .. } => "PtrFromParts",
        Inst::AtomicLoad { .. } => "AtomicLoad",
        Inst::AtomicStore { .. } => "AtomicStore",
        Inst::AtomicRMW { .. } => "AtomicRMW",
        Inst::CmpXchg { .. } => "CmpXchg",
        Inst::Fence { .. } => "Fence",
        Inst::Br { .. } => "Br",
        Inst::CondBr { .. } => "CondBr",
        Inst::Switch { .. } => "Switch",
        Inst::Call { .. } => "Call",
        Inst::CallIndirect { .. } => "CallIndirect",
        Inst::Return { .. } => "Return",
        Inst::ExtractField { .. } => "ExtractField",
        Inst::InsertField { .. } => "InsertField",
        Inst::ExtractElement { .. } => "ExtractElement",
        Inst::InsertElement { .. } => "InsertElement",
        Inst::Const { .. } => "Const",
        Inst::NullPtr => "NullPtr",
        Inst::GlobalAddr { .. } => "GlobalAddr",
        Inst::Undef { .. } => "Undef",
        Inst::Assume { .. } => "Assume",
        Inst::Assert { .. } => "Assert",
        Inst::Unreachable => "Unreachable",
        Inst::Copy { .. } => "Copy",
        Inst::Select { .. } => "Select",
        Inst::SeqMapAddK { .. } => "SeqMapAddK",
        Inst::SeqMapNot { .. } => "SeqMapNot",
        Inst::SeqMap { .. } => "SeqMap",
        Inst::Borrow { .. } => "Borrow",
        Inst::BorrowMut { .. } => "BorrowMut",
        Inst::EndBorrow { .. } => "EndBorrow",
        Inst::Retain { .. } => "Retain",
        Inst::Release { .. } => "Release",
        Inst::IsUnique { .. } => "IsUnique",
        Inst::Dealloc { .. } => "Dealloc",
        Inst::MemCopy { .. } => "MemCopy",
        Inst::MemSet { .. } => "MemSet",
        Inst::OpenFrame { .. } => "OpenFrame",
        Inst::BindSlot { .. } => "BindSlot",
        Inst::LoadSlot { .. } => "LoadSlot",
        Inst::CloseFrame { .. } => "CloseFrame",
        Inst::DialectOp(_) => "DialectOp",
        Inst::CoroSuspend { .. } => "CoroSuspend",
        Inst::Invoke { .. } => "Invoke",
        Inst::LandingPad { .. } => "LandingPad",
        Inst::Resume { .. } => "Resume",
        Inst::MakeAggregate { .. } => "MakeAggregate",
        Inst::MakeClosure { .. } => "MakeClosure",
        Inst::Drop { .. } => "Drop",
        Inst::ArraySplat { .. } => "ArraySplat",
        Inst::TensorContract { .. } => "TensorContract",
        Inst::TensorMap { .. } => "TensorMap",
        Inst::TensorReduce { .. } => "TensorReduce",
        Inst::TensorView { .. } => "TensorView",
        Inst::TensorGather { .. } => "TensorGather",
        Inst::TensorScatter { .. } => "TensorScatter",
        Inst::CallCannotUnwind { .. } => "CallCannotUnwind",
        Inst::CallIndirectCannotUnwind { .. } => "CallIndirectCannotUnwind",
        Inst::AssertInvoke { .. } => "AssertInvoke",
        Inst::DropInvoke { .. } => "DropInvoke",
        Inst::InvokeIndirect { .. } => "InvokeIndirect",
    }
}

/// Every `trust_ir::Inst` variant name, and whether the admission gate admits
/// some instance of it. `tests/fsym_ub_map.rs` checks it against the gate on
/// a catalog of instances; the oracle generator must produce every admitted
/// one (or name why it cannot).
pub const FSYM_INST_VARIANTS: &[(&str, bool)] = &[
    ("BinOp", true),
    ("UnOp", true),
    ("Overflow", true),
    ("ICmp", true),
    ("FCmp", true),
    ("Cast", true),
    ("Load", true),
    ("Store", true),
    ("Alloca", true),
    ("HeapAlloc", true),
    ("GEP", true),
    ("PtrData", true),
    ("PtrMetadata", true),
    ("PtrFromParts", true),
    ("AtomicLoad", true),
    ("AtomicStore", true),
    ("AtomicRMW", true),
    ("CmpXchg", true),
    ("Fence", true),
    ("Br", true),
    ("CondBr", true),
    ("Switch", true),
    ("Call", true),
    ("CallIndirect", false),
    ("Return", true),
    ("ExtractField", true),
    ("InsertField", true),
    ("ExtractElement", true),
    ("InsertElement", true),
    ("Const", true),
    ("NullPtr", true),
    ("GlobalAddr", true),
    ("Undef", false),
    ("Assume", true),
    ("Assert", true),
    ("Unreachable", true),
    ("Copy", true),
    ("Select", true),
    ("SeqMapAddK", true),
    ("SeqMapNot", true),
    ("SeqMap", false),
    ("Borrow", true),
    ("BorrowMut", true),
    ("EndBorrow", true),
    ("Retain", false),
    ("Release", false),
    ("IsUnique", false),
    ("Dealloc", true),
    ("MemCopy", true),
    ("MemSet", true),
    ("OpenFrame", false),
    ("BindSlot", false),
    ("LoadSlot", false),
    ("CloseFrame", false),
    ("DialectOp", false),
    ("TensorContract", false),
    ("TensorMap", false),
    ("TensorReduce", false),
    ("TensorView", false),
    ("TensorGather", false),
    ("TensorScatter", false),
    ("CoroSuspend", false),
    ("Invoke", false),
    ("LandingPad", true),
    ("Resume", false),
    ("MakeAggregate", true),
    // Flat scalar/thin-pointer value construction; invocation stays refused.
    ("MakeClosure", true),
    // v47: refused at admission (no destructor model).
    ("Drop", false),
    // v50: pure value construction, admitted like `MakeAggregate`.
    ("ArraySplat", true),
    // v53: refused at admission (a non-propagating call boundary; no
    // host-unwind model, and the interpreter refuses it too).
    ("CallCannotUnwind", false),
    ("CallIndirectCannotUnwind", false),
    // v54: refused at admission (a sited check with an unwind edge; no
    // panic-entry or host-unwind model). A sited `Assert` is refused too, but
    // an unsited one is still admitted, so `Assert` stays `true`.
    ("AssertInvoke", false),
    // v55 (amendment D): refused at admission (a drop with an unwind edge; no
    // destructor model, exactly as `Drop`).
    ("DropInvoke", false),
    // v56 (amendment D Part 2): refused at admission (an indirect call with an
    // unwind edge; no callee summary and no host-unwind model, as
    // `CallIndirect` and `Invoke`).
    ("InvokeIndirect", false),
];

/// The map's refusal of `inst`, if any: a site the instruction can raise
/// that fsym refuses outright, or one whose kind fsym owes no verdict for at
/// this instruction. `None` admits it (as far as the map is concerned).
pub fn fsym_map_refusal(module: &Module, inst: &Inst) -> Option<String> {
    let name = fsym_inst_variant_name(inst);
    let rows = raises_by_variant().get(name)?;
    let mut owed = None;
    for (site, stance) in rows {
        match *stance {
            FsymUbStance::Refused => {
                return Some(format!(
                    "{name} can raise interpreter UB `{}` ({}: {}), which fsym refuses",
                    site.message, site.function, site.class
                ));
            }
            FsymUbStance::Owed { kind, applies, .. } if applies(module, inst) => {
                let owed = owed.get_or_insert_with(|| fsym_owed_kinds(module, inst));
                if !owed.contains(&kind) {
                    return Some(format!(
                        "{name} can raise interpreter UB `{}` ({}: {}) and fsym owes no {kind:?} verdict for it",
                        site.message, site.function, site.class
                    ));
                }
            }
            FsymUbStance::Owed { .. }
            | FsymUbStance::AtSource { .. }
            | FsymUbStance::NotRaised(_)
            | FsymUbStance::Outside(_) => {}
        }
    }
    None
}

/// The map inverted: each raiser's `(site, stance)` rows, built once.
fn raises_by_variant()
-> &'static HashMap<&'static str, Vec<(&'static FsymInterpreterUbSite, FsymUbStance)>> {
    static ROWS: OnceLock<
        HashMap<&'static str, Vec<(&'static FsymInterpreterUbSite, FsymUbStance)>>,
    > = OnceLock::new();
    ROWS.get_or_init(|| {
        let mut rows: HashMap<_, Vec<_>> = HashMap::new();
        for site in FSYM_INTERPRETER_UB_SITES {
            for raise in site.raisers {
                for name in raise.by {
                    rows.entry(*name).or_default().push((site, raise.stance));
                }
            }
        }
        rows
    })
}

/// Whether an interpreter UB `message` is an instance of a site's message
/// key (the first characters of its literal, `{..}` holes matching any
/// text).
pub fn fsym_site_message_matches(key: &str, message: &str) -> bool {
    let mut literals = Vec::new();
    let mut rest = key;
    loop {
        match rest.find('{') {
            Some(open) => {
                literals.push(&rest[..open]);
                match rest[open..].find('}') {
                    Some(close) => rest = &rest[open + close + 1..],
                    None => break, // the key ends inside a hole
                }
            }
            None => {
                literals.push(rest);
                break;
            }
        }
    }
    let Some(first) = literals.first() else {
        return true;
    };
    if !message.starts_with(first) {
        return false;
    }
    let mut at = first.len();
    for literal in &literals[1..] {
        if literal.is_empty() {
            continue;
        }
        match message.get(at + 1..).and_then(|tail| tail.find(literal)) {
            Some(found) => at += 1 + found + literal.len(),
            None => return false,
        }
    }
    true
}

/// The class entry named `name`, if any.
pub fn fsym_ub_class(name: &str) -> Option<&'static crate::fsym_trust_ir::FsymUbClass> {
    FSYM_TRUST_IR_UB_CLASSES
        .iter()
        .find(|class| class.name == name)
}

/// The number of interpreter UB sites each class covers (the classes table
/// is checked against this in `tests/fsym_ub_map.rs`).
pub fn fsym_sites_per_class() -> Vec<(&'static str, usize)> {
    FSYM_TRUST_IR_UB_CLASSES
        .iter()
        .map(|class| {
            let sites = FSYM_INTERPRETER_UB_SITES
                .iter()
                .filter(|site| site.class == class.name)
                .count();
            (class.name, sites)
        })
        .collect()
}

/// Whether `class` is `Checked` with `kind`.
pub fn fsym_class_checks(
    class: &crate::fsym_trust_ir::FsymUbClass,
    kind: FsymTrustIrDiagnosticKind,
) -> bool {
    matches!(class.status, FsymUbClassStatus::Checked(checked) if checked == kind)
}
