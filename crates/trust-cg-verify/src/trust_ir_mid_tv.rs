// trust-cg-verify/trust_ir_mid_tv.rs - checkers for the trust-ir mid-end
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Independent checkers for the trust-ir → trust-ir mid-end (`trust-cg-irmid`).
//!
//! The mid-end rewrites one function at a time and hands each rewrite here as
//! a SOURCE function, a TARGET function and a [`PassWitness`] naming what the
//! pass claims it did. [`check_pass`] accepts the target only when
//!
//! 1. every claimed rewrite satisfies its side condition on the SOURCE, as
//!    derived here from the source function and module alone (the pass's own
//!    analyses are never consulted), and
//! 2. the target is EXACTLY the function this module rebuilds by applying the
//!    claimed rewrites to the source: any other difference, including a
//!    rewrite the witness does not name, refuses the target.
//!
//! Only constant-table promotion and the CRC-table rewrite change the module
//! beyond the function: their witnesses carry the types and globals they
//! append ([`PassWitness::module_additions`]), which are checked here
//! against the source module and are exactly what the caller appends.
//!
//! The side conditions, per pass:
//!
//! * **copy propagation** ([`CopyPropWitness`]): each forwarded value is the
//!   single result of a `copy` whose operand is the named root, or a forwarded
//!   value whose root is that root; the root has exactly the copy's type (this
//!   module's own typing, [`value_type`]); every use is renamed and the copies
//!   are removed. A `copy` is the identity on a value of its type, and its
//!   operand dominates it, so the root dominates every renamed use.
//! * **pure dead-code elimination** ([`DceWitness`]): each removed instruction
//!   is in this module's removable table ([`removal_class`]) with the class the
//!   witness states, and no remaining instruction uses one of its results.
//!   `insertfield` and `extractfield` are removable only over a value of their
//!   own aggregate type: the rustc bridge also writes them over a POINTER to
//!   the aggregate, which the wasm lane lowers as a store or load through it.
//!   An instruction whose definedness depends on its operands' VALUES
//!   (division, remainder, shifts (but a shift by a constant amount below
//!   its fixed width, or a division or remainder by a constant that cannot
//!   fault, is total), float-to-int conversions, int-to-pointer
//!   conversions from an integer wider than a wasm32 address, conversions to
//!   `bool`/`char`, an access or address
//!   computation from anything but a fresh allocation (an `alloca`,
//!   count-free or counted by an integer constant of at least 1) or a global,
//!   directly or through `gep`s by constants, `ptrtoptr`s and copies) is never
//!   removable: past it, execution knows something about
//!   those values, which may be an address's bits, and the wasm lane's
//!   capture analysis reads exactly that as the address being exposed
//!   (`wasm/lower/captures.rs`). Removing it would let the lane share the
//!   allocation's bytes where the source kept them. An `inttoptr` from an
//!   integer of at most 32 bits, `isize` or `usize` is total on a defined
//!   integer (the interpreter's address check cannot fail below the pointer
//!   width, and the lane's capture analysis, `trust_cg_irmid::escape`'s
//!   `cast_is_partial`, reads it as no exposure), so it is removable as a
//!   refinement (its operand may be poison).
//!   [`RemovalClass::Exact`] removals raise nothing on any input of a
//!   well-typed module; [`RemovalClass::Refinement`] removals may raise
//!   undefined behaviour on some inputs (the reference interpreter faults when
//!   arithmetic inspects poison, on a division by zero, an out-of-bounds
//!   access or address, an exhausted address space), so removing them only
//!   removes behaviour the source leaves undefined. They are counted apart.
//! * **constant-branch folding** ([`BranchFoldWitness`]): a `condbr` on a
//!   `const bool`, or a `switch` on an integer `const` whose cases are integer
//!   constants of its type, becomes `br` to the edge the interpreter takes
//!   (first matching case, else the default; a `switch` whose default is
//!   declared unreachable and that no case matches is not folded); a removed
//!   block is unreachable from the entry in the folded function and defines no
//!   value a remaining instruction uses.
//! * **pointer chain to byte-offset GEP** ([`PtrGepWitness`]):
//!   `inttoptr(ptrtoint(p) + k)` to `ptr`, or the round trip
//!   `inttoptr(ptrtoint(p))` (`k = 0`), with `p` a `ptr` lying `d` bytes into
//!   an `alloca` (count-free, or counted by an integer constant `k >= 1`) of
//!   `S > 0` bytes (the `alloca`, or a value derived from it by copies, `ptrtoptr`s and `gep`s by non-negative integer
//!   constants, every step inside it), the integer type at least as wide as a
//!   pointer, and `k` a constant expression of that type (an integer
//!   constant, the same-width `bitcast` of one, or an `add` or `mul` of two
//!   such, each step in `[0, 2^(bits - 1))`, so neither signedness nor
//!   wrapping changes its value) with `d + k < S`, becomes `gep u8, p, [k]`
//!   (`copy p` when `k = 0`). The reference interpreter resolves `inttoptr`
//!   to the allocation containing the address (`try_pointer_from_address`;
//!   allocations are bump-allocated, never overlap and are never reused):
//!   `p`'s allocation contains `addr(p) + k` exactly when `d + k < S`, so
//!   both forms are the pointer at offset `d + k` of `p`'s allocation.
//!   Outside that range the address may name a neighbour (or one past the
//!   end), and the chain is left.
//!
//! The memory checkers share one premise, the capture analysis's
//! (`trust_cg_irmid::escape`): an allocation whose address bits are never
//! observed, and which no value computed from its address leaves, is reached
//! only through those values. Each re-derives the shape it relies on from the
//! SOURCE with the interpreter's layout (`fsym_layout`):
//!
//! * **single-dominating-store forwarding** ([`StoreFwdWitness`]): the load
//!   and the store go through an UNOBSERVABLE SLOT — a count-free `alloca`
//!   whose every use is a plain load or store through it or a `gep u8|i8` of
//!   it by one constant whose every use is a plain load or store through it,
//!   every access inside it — at the same offset, with the same type and
//!   alignment; the type is one whose reload is the stored value
//!   (integers, `bool`, `char`, floats: not a pointer, which a reload
//!   re-resolves to whichever allocation contains its address), and the value
//!   is not `undef` and has exactly that type (this module's typing, or a
//!   call's declared return: a store may write a value of another type, such
//!   as an enum a call returns stored as its tag byte). Walking the CFG backward from the load over every path,
//!   the store is met before any store through the slot overlapping the
//!   load's bytes, the `alloca` itself (a fresh allocation: an undefined
//!   read), the stored value's definition, the entry, or a block without
//!   predecessors. So on every execution the load reads the bytes that store
//!   wrote from that value, and the load becomes `copy` of it — exact: the
//!   store executed at the same address, type and alignment, so the load is
//!   defined and returns the value. Partial overlaps, mixed widths and
//!   undefined reads are refused; the walk needs no reducible CFG (the pass
//!   still leaves irreducible ones alone).
//! * **dead slots** ([`DeadSlotWitness`]): the slot is unobservable and
//!   nothing loads from it, and the claimed stores are exactly its stores;
//!   they are removed, each a refinement (a store may be undefined, e.g.
//!   misaligned, where the target does nothing).
//! * **constant-table promotion** ([`CtpWitness`]): every value derived from
//!   the `alloca`'s address is a pointer of its provenance or an
//!   address-width integer equal to the address plus a displacement, moved
//!   only by `copy`, `gep` (indices not derived), `ptrtoint`, `bitcast`
//!   between address-width integers, `add` of an independent amount, `sub` of
//!   a constant, and `inttoptr` only where the displacement provably lies in
//!   the allocation (a constant, or an index bounded by its definition or by
//!   a dominating unsigned check, times a scale, plus a non-negative
//!   constant: then the address resolves to the allocation); it is never
//!   compared, branched on, returned, passed, stored or bound to a block
//!   parameter; every store through it writes an integer or `bool` constant
//!   at a known displacement inside it, no two disagree on a byte, and some
//!   load reads it. The `alloca` becomes `global_addr` of the next new
//!   global, which must be a fresh-named, internal, read-only `[u8 x size]`
//!   of exactly the image (bytes no store writes as 0) with the allocation's
//!   alignment, and the stores go. A refinement: a read of a byte before its
//!   store, or of one no store writes, is poison or undefined in the source
//!   and the image's byte in the target; every other read sees the same
//!   bytes, and nothing observes that the address moved.
//! * **scalar replacement** ([`SroaWitness`], `trust_ir_mid_tv_sroa.rs`): an
//!   unobservable slot (count-free or counted by a positive constant) reached
//!   through constant-offset `gep`s, `ptrtoptr`s, copies and the bridge's
//!   field access through a pointer, whose accesses each lie in one of its
//!   disjoint fields, becomes one SSA value per field joined by new block
//!   parameters; each load's claimed value is, on every backward path, the
//!   last store of its field, the start of the block whose new parameter it
//!   is, or the field's initial zero at the `alloca`, and each edge into
//!   such a block passes the value that reaches its end. Accesses of another
//!   type than the field's carrier are exact reinterpretations (`bitcast`,
//!   `ptrtoint`, `inttoptr`, `ptrtoptr`) of values never poison; a `ptr`
//!   carrier holds only addresses inside fresh allocations; a part of a
//!   field (a narrower access under a word copy) is shifted and masked out
//!   of, or into, the field's unsigned integer. Partial overlaps past a word,
//!   undefined reads of non-integer fields and irreducible CFGs are refused;
//!   each rewritten access is a refinement (it may be misaligned in the
//!   source, and a zero may stand for poison).
//! * **inlining** ([`InlineWitness`], `trust_ir_mid_tv_inline.rs`): a direct
//!   `call` of a non-recursive function whose body the call reaches (a
//!   linkage no other definition replaces) and which carries no proof
//!   material is replaced by its body, renamed into fresh values and blocks,
//!   the entry parameters bound to the arguments and the returns joined into
//!   the call's results (a thin pointer argument of another pointer type
//!   through a `ptrtoptr`). The target must also be a well-formed CFG defining
//!   each value once whose opcode multiset is the source's with each call
//!   replaced by its callee's (the OPT-4 inliner's conservation check). A
//!   refinement: the call boundary's own checks (no poison argument or result,
//!   exact argument types) go with the call.
//! * **range rules** ([`RangeWitness`], `trust_ir_mid_tv_range.rs`): the
//!   trust-ir form of the native lanes' LIR unsigned-range simplification. An
//!   `icmp` whose operands' intervals decide it (or a dominating compare of
//!   the same operands) becomes `const bool`, an `add`/`sub`/`mul.overflow`
//!   that cannot overflow becomes the plain arithmetic and `const bool
//!   false`, a `select`, `assert` or `condbr` on a decided condition becomes
//!   a `copy` of its arm, nothing, or a `br`, and a `switch` drops the cases
//!   outside its value's interval (and its default when the cases cover it);
//!   blocks the folded branches leave unreachable may go. Each rewrite names
//!   one interval premise per operand it reads, which must contain the
//!   interval this module derives for the operand in the rewrite's block:
//!   from its definition (constants, masks, extensions, non-wrapping
//!   arithmetic, shifts and remainders by known amounts, decided compares),
//!   narrowed by the conditions of the dominating edges that alone enter a
//!   block, and for a block parameter the witness's claimed interval, which
//!   is checked inductively on every edge into its block; the rule is decided
//!   on the premises.
//!   Exact: a value with an interval is never poison.
//! * **loop-invariant code motion** ([`LicmWitness`],
//!   `trust_ir_mid_tv_loop.rs`): a natural loop's header parameter every
//!   back edge passes back unchanged becomes the preheader's argument, and
//!   an instruction whose operands are defined outside the loop moves to the
//!   end of its preheader when it raises nothing on operands this module
//!   proves never poison, or when it is in the header after only quiet
//!   instructions (a non-volatile load only from a loop that writes,
//!   allocates and calls nothing, or whose only writes are non-volatile
//!   stores at constant offsets inside allocations disjoint from the
//!   load's bytes). Exact.
//! * **closed-form induction** ([`LoopCfWitness`], `trust_ir_mid_tv_loop.rs`):
//!   a counted loop (one exit, in its header, on `<u`, `<s` or `!=` of a
//!   `+ 1` induction variable against an invariant bound) whose only other
//!   values are affine accumulators of it is replaced by the trip count and
//!   each accumulator's final value computed at the end of the preheader;
//!   its removed instructions are all removable, so the rewrite is exact or
//!   a refinement by the dead-code table.
//! * **full unrolling** ([`UnrollWitness`], `trust_ir_mid_tv_unroll.rs`): a
//!   natural loop with one back edge, no inner cycle, an exit in its header
//!   on an `icmp` this module decides on every visit (its operands read as a
//!   constant, invariant or induction root plus a constant offset), and a
//!   trip count and copied size within [`MAX_UNROLL_TRIPS`] and
//!   [`MAX_UNROLLED_INSTS`], is replaced by its iterations: the header's
//!   parameters substituted per copy, side exits and the blocks they alone
//!   enter copied along, the original header running once on the last
//!   visit. Exact but for the copies of the exit compare it drops.
//! * **interval-bounded unrolling** ([`BoundedUnrollWitness`],
//!   `trust_ir_mid_tv_bounded.rs`): the same loops, with an exit test of any
//!   form in the header, whose header this module shows to leave on visit
//!   `B` (its induction variables are constants there; values from before
//!   the loop are read by intervals derived from their definitions), become
//!   `B` copies that keep their exit tests and a last visit that leaves;
//!   values of the loop are read outside it only by exit blocks, which each
//!   copy takes along. Exact.
//! * **select-branch rules** ([`SelectBranchWitness`],
//!   `trust_ir_mid_tv_selbr.rs`): a `switch` or `condbr` whose scrutinee this
//!   module's evaluator decides under each value of a named `bool` becomes a
//!   branch on it (a refinement); the blocks it leaves unreachable go; under
//!   an edge that fixes that `bool`, an operand that is a `select` on it
//!   behind casts reads its arm through copies of the casts (exact).
//! * **CRC-table rewrite** ([`CrcTableWitness`], `trust_ir_mid_tv_crctable.rs`):
//!   a pure acyclic region of integer operations whose one input this module
//!   bounds below 256 by its definition becomes a load from a read-only
//!   table of the region's 256 results, each computed here by running the
//!   region, its xors all of one polynomial. Exact.
//! * **induction-variable strength reduction** ([`IvSrWitness`],
//!   `trust_ir_mid_tv_ivsr.rs`): loop values that read as `A * i + R + c`
//!   of an induction variable `i` (a constant step) become `q + c` of a new
//!   header parameter `q` starting at `A * i0 + R` and stepping by `A * s`;
//!   the inductive invariant is distributivity modulo the width, and the
//!   preheader's computation reads only values never poison. Exact.
//! * **constant folding and algebraic simplification** ([`ConstFoldWitness`],
//!   [`SimplifyWitness`], `trust_ir_mid_tv_fold.rs`): an instruction of
//!   constant operands becomes the constant the interpreter computes (exact,
//!   only where it raises nothing); an identity element, a mask over an
//!   extension, a truncated extension, a bitcast round trip and the parts of
//!   a packed pair become `copy`s or a narrower `trunc`, and a rotate whose
//!   every use masks only the bits it brings round becomes a right shift by
//!   a fresh constant, and an address minus its base becomes the offset
//!   (refinements).
//! * **address folding, dead block parameters and block merging**
//!   ([`AddrFoldWitness`], [`DeadParamWitness`], [`BlockMergeWitness`],
//!   `trust_ir_mid_tv_addr.rs`): an `inttoptr` whose integer reads as a
//!   dominating allocation's address plus an offset inside it becomes a
//!   `gep` of it; a block parameter that computes nothing goes with its
//!   arguments; a block one edge enters takes that edge's arguments and, along
//!   a `br`, joins its predecessor. Exact.
//!
//! What the witness check does NOT establish: nothing about the module's other
//! functions, and nothing about proof tables (the mid-end transports those
//! through trust-ir's `ProofTableTransformTransaction`). It is a structural
//! check of one rewrite against its own side conditions.
//!
//! The second, differential leg runs the source and the target function in
//! the reference interpreter (`trust_ir::interpret`) on the same seeded
//! inputs, under the refinement rule: an input on which the source raises
//! undefined behaviour (or violates an `assume`) is EXCLUDED, since the
//! target may do anything there. On every other input the target must give
//! the same outcome: the same results, the same bytes in the memory the
//! input provided, or the same structured panic. Runs the interpreter cannot
//! finish (an unsupported construct, a call to a declaration, a type error,
//! exhausted fuel) are counted as not executed, never as agreement.
//!
//! [`Harness`] (`trust_ir_mid_tv_harness.rs`) builds the inputs: scalars for
//! scalar parameters, and for pointer, slice and by-value aggregate
//! parameters a memory image planned from the function's own accesses and
//! the interpreter's layout, which a driver function allocates and passes
//! (two of a function's inputs bind its pointer parameters into one object);
//! the function's callees in the module run through the call (to a call
//! depth); a run's fuel is sized from the function and its loops and reached
//! through a ladder; and the runs interpret a view of the module that spells
//! the rustc bridge's lane idioms in the interpreter's typed forms. Its
//! module documentation states what each covers and what it does not.
//! [`seeded_inputs`], [`run_samples`] and [`compare_samples`] are the
//! scalar-only form the harness builds on (a function of scalar parameters
//! gets exactly [`seeded_inputs`]' inputs).
//!
//! What the differential does NOT establish: anything on the inputs it did
//! not draw (aliasing between pointer parameters is drawn in two
//! arrangements only), on the inputs it excluded or could not run, about
//! memory the input did not provide (a store to a global is observed only
//! through what the function returns or writes back) or bytes the source
//! left uninitialised, or about a function no input can be built for (a
//! function pointer, closure, trait object or handle parameter). Coverage
//! is reported as counts, by reason, never implied.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::panic::{AssertUnwindSafe, catch_unwind};

use trust_ir::interpret::{
    InterpretErrorCode, InterpretOptions, InterpretPanic, InterpretValue, InterpretValueKind,
    Interpreter,
};
use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, BlockId, CastOp, Constant, Function, Global, ICmpOp, Inst, Module, Ty, ValueId,
};

use crate::fsym_layout::FsymLayout;

#[path = "trust_ir_mid_tv_addr.rs"]
mod addr;
#[path = "trust_ir_mid_tv_argpromo.rs"]
mod argpromo;
#[path = "trust_ir_mid_tv_bounded.rs"]
mod bounded;
#[path = "trust_ir_mid_tv_byaddr.rs"]
mod byaddr;
#[path = "trust_ir_mid_tv_bytecopy.rs"]
mod bytecopy;
#[path = "trust_ir_mid_tv_crctable.rs"]
mod crctable;
#[path = "trust_ir_mid_tv_fillcall.rs"]
mod fillcall;
#[path = "trust_ir_mid_tv_fold.rs"]
mod fold;
#[path = "trust_ir_mid_tv_inline.rs"]
mod inline;
#[path = "trust_ir_mid_tv_ivsr.rs"]
mod ivsr;
#[path = "trust_ir_mid_tv_lanes.rs"]
mod lanes;
#[path = "trust_ir_mid_tv_loop.rs"]
mod loops;
#[path = "trust_ir_mid_tv_memcall.rs"]
mod memcall;
#[path = "trust_ir_mid_tv_memcmp.rs"]
mod memcmp;
#[path = "trust_ir_mid_tv_range.rs"]
mod range;
#[path = "trust_ir_mid_tv_selbr.rs"]
mod selbr;
#[path = "trust_ir_mid_tv_sroa.rs"]
mod sroa;
#[path = "trust_ir_mid_tv_unroll.rs"]
mod unroll;
pub use addr::{
    AddrFold, AddrFoldWitness, BlockMerge, BlockMergeWitness, DeadParam, DeadParamWitness,
    FieldAccess, FieldAccessWitness,
};
pub use argpromo::{
    ARGPROMO_CLONE_MARK, ArgPromoField, ArgPromoParam, ArgPromoSite, ArgPromoWitness,
    argpromo_clone_name,
};
pub use bounded::{BoundedUnrollLoop, BoundedUnrollWitness, MAX_BOUNDED_TRIPS};
pub use byaddr::{ByAddrParam, ByAddrSite, ByAddrWitness, byaddr_clone_name};
pub use bytecopy::{ByteCopyForward, ByteCopyRun, ByteCopyWitness, ForwardedStore};
pub use crctable::{CRC_TABLE_ENTRIES, CrcTable, CrcTableWitness};
pub use fillcall::{FillCall, FillCallWitness};
pub use fold::{
    ConstFold, ConstFoldWitness, Respell, RespellRule, RespellWitness, Simplify, SimplifyRule,
    SimplifyWitness,
};
pub use inline::{InlineSite, InlineWitness, MAX_SPLICED_SLOT_BYTES};
pub use ivsr::{IvSrLoop, IvSrStrand, IvSrUse, IvSrWitness};
pub use lanes::{LaneLoad, LaneLoadWitness, LaneRead};
pub use loops::{LicmLoop, LicmWitness, LoopCfLoop, LoopCfWitness};
pub use memcall::{MemCall, MemCallWitness};
pub use memcmp::{MAX_MEMCMP_BYTES, MemCmp, MemCmpWitness};
pub use range::{
    RangeInvariant, RangeLemma, RangePremise, RangeRewrite, RangeRule, RangeWitness,
    range_fact_lemmas, range_obligations,
};
pub use selbr::{MAX_FORWARD_CHAIN, SelectBranchWitness, SelectForward, SelectTerminator};
pub use sroa::{
    SroaField, SroaIncoming, SroaLoad, SroaMerge, SroaParam, SroaSlot, SroaStore, SroaWitness,
};
pub use unroll::{MAX_UNROLL_TRIPS, MAX_UNROLLED_INSTS, UnrollLoop, UnrollWitness};

// ---------------------------------------------------------------------------
// Witnesses
// ---------------------------------------------------------------------------

/// What removing one dead instruction does to the program's behaviour.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RemovalClass {
    /// The instruction raises nothing on any input of a well-typed module: a
    /// constant, a global's address, `undef`, or a `copy` of a value of its
    /// own type. Removing it unused preserves behaviour exactly.
    Exact,
    /// The instruction may raise undefined behaviour on some inputs (it
    /// inspects its operands, accesses memory, computes an address, or
    /// allocates). Removing it unused is a REFINEMENT: the target is defined
    /// where the source was not, and equal everywhere else.
    Refinement,
}

impl RemovalClass {
    /// Stable name for evidence.
    pub const fn as_str(self) -> &'static str {
        match self {
            RemovalClass::Exact => "exact",
            RemovalClass::Refinement => "refinement",
        }
    }
}

/// A forwarded `copy`: every use of `copy` becomes a use of `root`, and the
/// `copy` instruction is removed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CopyForward {
    pub copy: ValueId,
    pub root: ValueId,
}

/// Copy propagation's claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CopyPropWitness {
    pub forwards: Vec<CopyForward>,
}

/// One removed instruction, addressed in the SOURCE function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeadRemoval {
    pub block: BlockId,
    pub index: usize,
    pub results: Vec<ValueId>,
    pub class: RemovalClass,
}

/// Pure dead-code elimination's claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DceWitness {
    pub removals: Vec<DeadRemoval>,
}

/// A terminator of `block` folded to `br target`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchFold {
    pub block: BlockId,
    pub target: BlockId,
}

/// Constant-branch folding's claim: the folds, then the blocks removed as
/// unreachable from the entry of the folded function.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BranchFoldWitness {
    pub folds: Vec<BranchFold>,
    pub removed_blocks: Vec<BlockId>,
}

/// One `inttoptr(ptrtoint(base) + offset_value)` at `(block, index)` of the
/// SOURCE, defining `result`, rewritten in place; `offset` is the value of
/// `offset_value`. For the round trip `inttoptr(ptrtoint(base))`,
/// `offset_value` names the `ptrtoint` and `offset` is 0. When `folded` is
/// set (an offset computed by a constant expression), the `gep` indexes by
/// that fresh value, defined by `const <integer type> offset` inserted just
/// before it, so the slot passes see a constant index (additive field,
/// pending the owner's sign-off on the mid-end's witnesses).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GepRewrite {
    pub block: BlockId,
    pub index: usize,
    pub result: ValueId,
    pub base: ValueId,
    pub offset: u64,
    pub offset_value: ValueId,
    pub folded: Option<ValueId>,
}

/// The pointer-chain pass's claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PtrGepWitness {
    pub rewrites: Vec<GepRewrite>,
}

/// One load at `(block, index)` of the SOURCE, defining `result`, replaced
/// by `copy` of `value`, the value the store at `(store_block, store_index)`
/// writes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoadForward {
    pub block: BlockId,
    pub index: usize,
    pub result: ValueId,
    pub store_block: BlockId,
    pub store_index: usize,
    pub value: ValueId,
}

/// Single-dominating-store forwarding's claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StoreFwdWitness {
    pub forwards: Vec<LoadForward>,
}

/// The stores, at `(block, index)` of the SOURCE, of a slot nothing reads.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeadSlot {
    pub alloca: ValueId,
    pub stores: Vec<(BlockId, usize)>,
}

/// Dead-slot removal's claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DeadSlotWitness {
    pub slots: Vec<DeadSlot>,
}

/// The `alloca` at `(block, index)` of the SOURCE, defining `alloca`,
/// replaced by the address of the new read-only `global`, and the stores
/// that initialized it, removed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CtpPromotion {
    pub block: BlockId,
    pub index: usize,
    pub alloca: ValueId,
    pub global: GlobalId,
    pub stores: Vec<(BlockId, usize)>,
}

/// Constant-table promotion's claim, with the module entries it appends:
/// `new_types` after the module's types, `new_globals` after its globals
/// (the `j`-th promotion's global is the `j`-th new one).
#[derive(Debug, Clone, Default, PartialEq)]
pub struct CtpWitness {
    pub promotions: Vec<CtpPromotion>,
    pub new_types: Vec<Ty>,
    pub new_globals: Vec<Global>,
}

/// A pass's claim about one function.
#[derive(Debug, Clone, PartialEq)]
pub enum PassWitness {
    CopyProp(CopyPropWitness),
    Dce(DceWitness),
    BranchFold(BranchFoldWitness),
    PtrGep(PtrGepWitness),
    StoreFwd(StoreFwdWitness),
    DeadSlot(DeadSlotWitness),
    Ctp(CtpWitness),
    Sroa(SroaWitness),
    Inline(InlineWitness),
    Range(RangeWitness),
    ArgPromo(ArgPromoWitness),
    Licm(LicmWitness),
    LoopCf(LoopCfWitness),
    ConstFold(ConstFoldWitness),
    Unroll(UnrollWitness),
    AddrFold(AddrFoldWitness),
    DeadParam(DeadParamWitness),
    Simplify(SimplifyWitness),
    BlockMerge(BlockMergeWitness),
    IvSr(IvSrWitness),
    FieldAccess(FieldAccessWitness),
    MemCall(MemCallWitness),
    FillCall(FillCallWitness),
    ByteCopy(ByteCopyWitness),
    CrcTable(CrcTableWitness),
    SelectBranch(SelectBranchWitness),
    BoundedUnroll(BoundedUnrollWitness),
    LaneLoad(LaneLoadWitness),
    Respell(RespellWitness),
    MemCmp(MemCmpWitness),
    ByAddr(ByAddrWitness),
}

impl PassWitness {
    /// Number of claimed rewrites.
    pub fn rewrite_count(&self) -> usize {
        match self {
            PassWitness::CopyProp(w) => w.forwards.len(),
            PassWitness::Dce(w) => w.removals.len(),
            PassWitness::BranchFold(w) => w.folds.len() + w.removed_blocks.len(),
            PassWitness::PtrGep(w) => w.rewrites.len(),
            PassWitness::StoreFwd(w) => w.forwards.len(),
            PassWitness::DeadSlot(w) => w.slots.iter().map(|s| s.stores.len()).sum(),
            PassWitness::Ctp(w) => w.promotions.len(),
            PassWitness::Sroa(w) => w.rewrite_count(),
            PassWitness::Inline(w) => w.rewrite_count(),
            PassWitness::Range(w) => w.rewrite_count(),
            PassWitness::ArgPromo(w) => w.rewrite_count(),
            PassWitness::Licm(w) => w.rewrite_count(),
            PassWitness::LoopCf(w) => w.rewrite_count(),
            PassWitness::ConstFold(w) => w.folds.len(),
            PassWitness::Unroll(w) => w.rewrite_count(),
            PassWitness::AddrFold(w) => w.folds.len(),
            PassWitness::DeadParam(w) => w.params.len(),
            PassWitness::Simplify(w) => w.rewrites.len(),
            PassWitness::BlockMerge(w) => w.merges.len(),
            PassWitness::IvSr(w) => w.rewrite_count(),
            PassWitness::FieldAccess(w) => w.rewrites.len(),
            PassWitness::MemCall(w) => w.rewrites.len(),
            PassWitness::FillCall(w) => w.rewrites.len(),
            PassWitness::ByteCopy(w) => w.rewrite_count(),
            PassWitness::CrcTable(w) => w.tables.len(),
            PassWitness::SelectBranch(w) => w.rewrite_count(),
            PassWitness::BoundedUnroll(w) => w.rewrite_count(),
            PassWitness::LaneLoad(w) => w.rewrite_count(),
            PassWitness::Respell(w) => w.rewrites.len(),
            PassWitness::MemCmp(w) => w.rewrites.len(),
            PassWitness::ByAddr(w) => w.rewrite_count(),
        }
    }

    /// The types and globals the rewrite appends to the module (empty for
    /// every pass but constant-table promotion and the CRC-table rewrite).
    pub fn module_additions(&self) -> (&[Ty], &[Global]) {
        match self {
            PassWitness::Ctp(w) => (&w.new_types, &w.new_globals),
            PassWitness::CrcTable(w) => (&w.new_types, &w.new_globals),
            _ => (&[], &[]),
        }
    }

    /// The signatures and functions the rewrite appends to the module (empty
    /// for every pass but argument promotion, whose clones they are).
    pub fn function_additions(&self) -> (&[trust_ir::FuncTy], &[Function]) {
        match self {
            PassWitness::ArgPromo(w) => (&w.new_func_types, &w.new_functions),
            PassWitness::ByAddr(w) => (&w.new_func_types, &w.new_functions),
            _ => (&[], &[]),
        }
    }
}

/// What an accepted witness established.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct WitnessVerdict {
    /// Rewrites checked exact.
    pub exact: usize,
    /// Rewrites checked as refinements (dead UB-raising instructions removed).
    pub refinements: usize,
}

/// Why a witness was refused. Every refusal rolls the pass back on the
/// function; none refuses the program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MidTvError {
    /// The named value is not defined the way the witness says.
    NoDefinition {
        value: ValueId,
        expected: &'static str,
    },
    /// A forwarded copy's operand does not lead to the claimed root.
    WrongRoot { copy: ValueId, root: ValueId },
    /// A forwarded copy's root does not have the copy's type (or its type is
    /// unknown to this module's typing).
    TypeChange { copy: ValueId },
    /// A value is forwarded twice, or a root is itself forwarded.
    InconsistentForwarding { value: ValueId },
    /// A claimed removal names no instruction of the source.
    NoInstruction { block: BlockId, index: usize },
    /// A removal names an instruction that is not removable.
    Effectful { block: BlockId, index: usize },
    /// A removal's class differs from this module's classification.
    WrongClass {
        block: BlockId,
        index: usize,
        claimed: RemovalClass,
        derived: RemovalClass,
    },
    /// A removed value is still used.
    RemovedValueUsed { value: ValueId },
    /// A fold names a block whose terminator does not branch on a constant.
    NotConstantBranch { block: BlockId },
    /// A fold names a target other than the edge the constant selects.
    WrongTarget {
        block: BlockId,
        claimed: BlockId,
        derived: BlockId,
    },
    /// A removed block is reachable from the entry of the folded function.
    ReachableBlockRemoved { block: BlockId },
    /// A pointer-chain rewrite's shape does not hold on the source.
    NotPointerChain { value: ValueId, why: &'static str },
    /// A pointer-chain rewrite's offset is not inside the allocation.
    OffsetOutOfBounds {
        value: ValueId,
        offset: u64,
        size: u64,
    },
    /// A claimed slot's address is observable (or it is no allocation).
    SlotObservable { slot: ValueId, why: &'static str },
    /// A forwarded load's shape, or its store's, does not hold on the source.
    NotForwardable { load: ValueId, why: &'static str },
    /// Some path reaches the load without the claimed store as the last
    /// write of its bytes.
    NoUniqueReachingStore { load: ValueId, why: &'static str },
    /// A promoted allocation is not a constant table on the source.
    NotPromotable { alloca: ValueId, why: String },
    /// A global constant-table promotion or the CRC-table rewrite appends
    /// is not the table's read-only image.
    BadGlobal { why: String },
    /// A slot claimed for scalar replacement is not one on the source.
    NotScalarizable { alloca: ValueId, why: &'static str },
    /// A claimed inline site (the `site`-th of the witness) or its callee
    /// does not admit the splice.
    NotInlinable { site: usize, why: String },
    /// A site's claimed argument binding is not the call's.
    WrongBinding { site: usize, why: String },
    /// A site's renaming is not fresh and one-to-one.
    NotFresh { site: usize, why: String },
    /// The target's instructions are not the source's with each call
    /// replaced by its callee's body and binding.
    NotConserved { detail: String },
    /// The target's CFG is not well formed.
    MalformedCfg { detail: String },
    /// A range rewrite's premise is not implied by the fact this module
    /// derives for its value (`derived` is `None` when it derives none).
    RangePremise {
        value: ValueId,
        claimed: (u128, u128),
        derived: Option<(u128, u128)>,
    },
    /// A range rewrite names an instruction that is not its rule's form, or
    /// whose premises do not establish the rule's precondition.
    RangeUndecided {
        block: BlockId,
        index: usize,
        why: &'static str,
    },
    /// A claimed block-parameter interval of the range rules is malformed
    /// or does not hold on some edge into its block.
    RangeInvariant {
        block: BlockId,
        value: ValueId,
        why: &'static str,
    },
    /// A claimed argument-promotion site (the `site`-th of the witness), its
    /// callee, slot or clone does not admit the promotion.
    NotPromotableArgument { site: usize, why: String },
    /// A claimed loop rewrite (invariant code motion or closed-form
    /// induction) does not hold on the source's loop at `header`.
    NotLoopRewrite { header: BlockId, why: String },
    /// A claimed constant fold does not evaluate, on the source's constant
    /// operands, to the claimed constant.
    NotConstantFold { value: ValueId, why: String },
    /// A claimed algebraic simplification's identity does not hold on the
    /// instruction.
    NotSimplification { value: ValueId, why: String },
    /// A claimed address fold does not read as its base plus its offset
    /// inside the allocation.
    NotAddressFold { value: ValueId, why: String },
    /// A claimed dead block parameter is used, or its edges cannot drop it.
    NotDeadParam { value: ValueId, why: String },
    /// A claimed block merge's block is not entered by one edge of the
    /// claimed form.
    NotBlockMerge { block: BlockId, why: String },
    /// A claimed field-access rewrite is not a field access through a
    /// pointer of the claimed lane.
    NotFieldAccess { value: ValueId, why: String },
    /// A claimed memory-call rewrite is not a call of the C library's
    /// `memmove`, `memcpy` or `memset` declaration with a constant count
    /// whose result is unused.
    NotMemCall { value: ValueId, why: String },
    /// A claimed lane-load rewrite is not an array load of scalars read lane
    /// by lane as claimed.
    NotLaneLoad { value: ValueId, why: String },
    /// A claimed comparison-call rewrite is not a call of the `memcmp` or
    /// `bcmp` declaration with a small constant count expanded as claimed.
    NotMemCmp { value: ValueId, why: String },
    /// A claimed by-address clone site is not admissible as claimed.
    NotByAddr { site: usize, why: String },
    /// A claimed fill-call rewrite is not a call of the bridge's array-fill
    /// helper declaration with constant arguments filling one byte.
    NotFillCall {
        block: BlockId,
        index: usize,
        why: String,
    },
    /// A claimed byte-copy run or forward is not the copy it claims.
    NotByteCopy {
        block: BlockId,
        index: usize,
        why: String,
    },
    /// A claimed CRC-table rewrite's region is not a pure function of one
    /// byte that the table holds.
    NotCrcTable { block: BlockId, why: String },
    /// A claimed select-branch rewrite's terminator is not decided by the
    /// condition, or its forward is not guarded by it.
    NotSelectBranch { block: BlockId, why: String },
    /// The target is not the function the claimed rewrites produce.
    TargetDiffers { detail: String },
}

impl std::fmt::Display for MidTvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MidTvError::NoDefinition { value, expected } => {
                write!(f, "%{value} is not defined by {expected}")
            }
            MidTvError::WrongRoot { copy, root } => {
                write!(f, "copy %{copy} does not forward to %{root}")
            }
            MidTvError::TypeChange { copy } => {
                write!(
                    f,
                    "copy %{copy} changes the type of its operand (or the type is unknown)"
                )
            }
            MidTvError::InconsistentForwarding { value } => {
                write!(f, "%{value} is forwarded inconsistently")
            }
            MidTvError::NoInstruction { block, index } => {
                write!(f, "no instruction {index} in block {block}")
            }
            MidTvError::Effectful { block, index } => {
                write!(
                    f,
                    "instruction {index} of block {block} is not removable (effect or terminator)"
                )
            }
            MidTvError::WrongClass {
                block,
                index,
                claimed,
                derived,
            } => write!(
                f,
                "instruction {index} of block {block} is claimed {} but its removal is {}",
                claimed.as_str(),
                derived.as_str()
            ),
            MidTvError::RemovedValueUsed { value } => {
                write!(f, "removed value %{value} is still used")
            }
            MidTvError::NotConstantBranch { block } => {
                write!(f, "block {block} does not end in a branch on a constant")
            }
            MidTvError::WrongTarget {
                block,
                claimed,
                derived,
            } => write!(
                f,
                "block {block} folds to {claimed}, but its constant selects {derived}"
            ),
            MidTvError::ReachableBlockRemoved { block } => {
                write!(f, "removed block {block} is reachable")
            }
            MidTvError::NotPointerChain { value, why } => {
                write!(f, "%{value} is not an in-bounds pointer chain: {why}")
            }
            MidTvError::OffsetOutOfBounds {
                value,
                offset,
                size,
            } => write!(
                f,
                "%{value}: offset {offset} is outside the {size}-byte allocation"
            ),
            MidTvError::SlotObservable { slot, why } => {
                write!(f, "slot %{slot} is not unobservable: {why}")
            }
            MidTvError::NotForwardable { load, why } => {
                write!(f, "load %{load} is not forwardable: {why}")
            }
            MidTvError::NoUniqueReachingStore { load, why } => {
                write!(f, "load %{load} has no unique reaching store: {why}")
            }
            MidTvError::NotPromotable { alloca, why } => {
                write!(f, "allocation %{alloca} is not a constant table: {why}")
            }
            MidTvError::BadGlobal { why } => write!(f, "promoted global: {why}"),
            MidTvError::NotScalarizable { alloca, why } => {
                write!(f, "slot %{alloca} is not scalarizable: {why}")
            }
            MidTvError::NotInlinable { site, why } => {
                write!(f, "inline site {site} is not inlinable: {why}")
            }
            MidTvError::WrongBinding { site, why } => {
                write!(f, "inline site {site} binds wrongly: {why}")
            }
            MidTvError::NotFresh { site, why } => {
                write!(f, "inline site {site} renames into used names: {why}")
            }
            MidTvError::NotConserved { detail } => {
                write!(f, "inlining does not conserve the instructions: {detail}")
            }
            MidTvError::MalformedCfg { detail } => {
                write!(f, "the inlined CFG is malformed: {detail}")
            }
            MidTvError::RangePremise {
                value,
                claimed,
                derived,
            } => match derived {
                Some((lo, hi)) => write!(
                    f,
                    "%{value} is claimed in [{}, {}] but derives only [{lo}, {hi}]",
                    claimed.0, claimed.1
                ),
                None => write!(
                    f,
                    "%{value} is claimed in [{}, {}] but has no derived interval",
                    claimed.0, claimed.1
                ),
            },
            MidTvError::RangeUndecided { block, index, why } => {
                write!(
                    f,
                    "range rule at instruction {index} of block {block}: {why}"
                )
            }
            MidTvError::RangeInvariant { block, value, why } => {
                write!(f, "range invariant of %{value} in block {block}: {why}")
            }
            MidTvError::NotPromotableArgument { site, why } => {
                write!(f, "argument promotion site {site} is not admitted: {why}")
            }
            MidTvError::NotLoopRewrite { header, why } => {
                write!(f, "loop at block {header} is not rewritable: {why}")
            }
            MidTvError::NotConstantFold { value, why } => {
                write!(f, "%{value} does not fold to the claimed constant: {why}")
            }
            MidTvError::NotSimplification { value, why } => {
                write!(
                    f,
                    "%{value} is not simplified by the claimed identity: {why}"
                )
            }
            MidTvError::NotAddressFold { value, why } => {
                write!(f, "%{value} is not a folded address: {why}")
            }
            MidTvError::NotDeadParam { value, why } => {
                write!(f, "%{value} is not a dead block parameter: {why}")
            }
            MidTvError::NotBlockMerge { block, why } => {
                write!(f, "block {block} cannot be merged: {why}")
            }
            MidTvError::NotFieldAccess { value, why } => {
                write!(f, "%{value} is not a field access through a pointer: {why}")
            }
            MidTvError::NotMemCall { value, why } => {
                write!(f, "%{value} is not a rewritable memory library call: {why}")
            }
            MidTvError::NotLaneLoad { value, why } => {
                write!(f, "%{value} is not an array load read lane by lane: {why}")
            }
            MidTvError::NotMemCmp { value, why } => {
                write!(f, "%{value} is not an expandable comparison call: {why}")
            }
            MidTvError::NotByAddr { site, why } => {
                write!(f, "by-address site {site} is refused: {why}")
            }
            MidTvError::NotByteCopy { block, index, why } => {
                write!(
                    f,
                    "instruction {index} of block {block} is not the claimed byte copy: {why}"
                )
            }
            MidTvError::NotFillCall { block, index, why } => {
                write!(
                    f,
                    "instruction {index} of block {block} is not a rewritable array-fill call: {why}"
                )
            }
            MidTvError::NotCrcTable { block, why } => {
                write!(
                    f,
                    "the region from block {block} is not the claimed table lookup: {why}"
                )
            }
            MidTvError::NotSelectBranch { block, why } => {
                write!(
                    f,
                    "block {block}: not the claimed select-branch rewrite: {why}"
                )
            }
            MidTvError::TargetDiffers { detail } => {
                write!(f, "target differs from the claimed rewrite: {detail}")
            }
        }
    }
}

impl std::error::Error for MidTvError {}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Check `witness` against `source` (a function of `module`) and `target`.
/// `pointer_bits` is the target's pointer width.
pub fn check_pass(
    module: &Module,
    pointer_bits: u32,
    source: &Function,
    target: &Function,
    witness: &PassWitness,
) -> Result<WitnessVerdict, MidTvError> {
    let (expected, verdict) = match witness {
        PassWitness::CopyProp(w) => rebuild_copy_prop(module, source, w)?,
        PassWitness::Dce(w) => rebuild_dce(module, source, w)?,
        PassWitness::BranchFold(w) => rebuild_branch_fold(source, pointer_bits, w)?,
        PassWitness::PtrGep(w) => rebuild_ptr_gep(module, pointer_bits, source, w)?,
        PassWitness::StoreFwd(w) => rebuild_store_fwd(module, source, w)?,
        PassWitness::DeadSlot(w) => rebuild_dead_slot(module, source, w)?,
        PassWitness::Ctp(w) => rebuild_ctp(module, pointer_bits, source, w)?,
        PassWitness::Sroa(w) => sroa::rebuild_sroa(module, pointer_bits, source, w)?,
        PassWitness::Inline(w) => inline::rebuild_inline(module, source, target, w)?,
        PassWitness::Range(w) => range::rebuild_range(module, pointer_bits, source, w)?,
        PassWitness::ArgPromo(w) => argpromo::rebuild_argpromo(module, source, w)?,
        PassWitness::Licm(w) => loops::rebuild_licm(module, pointer_bits, source, w)?,
        PassWitness::LoopCf(w) => loops::rebuild_loop_cf(pointer_bits, source, w)?,
        PassWitness::ConstFold(w) => fold::rebuild_const_fold(pointer_bits, source, w)?,
        PassWitness::Unroll(w) => unroll::rebuild_unroll(pointer_bits, module, source, w)?,
        PassWitness::AddrFold(w) => addr::rebuild_addr_fold(module, pointer_bits, source, w)?,
        PassWitness::DeadParam(w) => addr::rebuild_dead_param(source, w)?,
        PassWitness::Simplify(w) => fold::rebuild_simplify(pointer_bits, source, w)?,
        PassWitness::BlockMerge(w) => addr::rebuild_block_merge(source, w)?,
        PassWitness::IvSr(w) => ivsr::rebuild_ivsr(pointer_bits, source, w)?,
        PassWitness::FieldAccess(w) => addr::rebuild_field_access(module, source, w)?,
        PassWitness::MemCall(w) => memcall::rebuild_mem_call(module, pointer_bits, source, w)?,
        PassWitness::FillCall(w) => fillcall::rebuild_fill_call(module, pointer_bits, source, w)?,
        PassWitness::ByteCopy(w) => bytecopy::rebuild_byte_copy(module, source, w)?,
        PassWitness::CrcTable(w) => crctable::rebuild_crc_table(module, pointer_bits, source, w)?,
        PassWitness::SelectBranch(w) => {
            selbr::rebuild_select_branch(module, pointer_bits, source, w)?
        }
        PassWitness::BoundedUnroll(w) => bounded::rebuild_bounded_unroll(pointer_bits, source, w)?,
        PassWitness::LaneLoad(w) => lanes::rebuild_lane_load(module, source, w)?,
        PassWitness::Respell(w) => fold::rebuild_respell(pointer_bits, source, w)?,
        PassWitness::MemCmp(w) => memcmp::rebuild_mem_cmp(module, pointer_bits, source, w)?,
        PassWitness::ByAddr(w) => byaddr::rebuild_byaddr(module, source, w)?,
    };
    if &expected != target {
        return Err(MidTvError::TargetDiffers {
            detail: first_difference(&expected, target),
        });
    }
    Ok(verdict)
}

/// The first place two functions differ, for the refusal's text.
fn first_difference(expected: &Function, target: &Function) -> String {
    if expected.blocks.len() != target.blocks.len() {
        return format!(
            "{} blocks expected, {} found",
            expected.blocks.len(),
            target.blocks.len()
        );
    }
    for (e, t) in expected.blocks.iter().zip(&target.blocks) {
        if e.id != t.id || e.params != t.params {
            return format!("block {} header", e.id);
        }
        if e.body.len() != t.body.len() {
            return format!(
                "block {}: {} instructions expected, {} found",
                e.id,
                e.body.len(),
                t.body.len()
            );
        }
        for (index, (en, tn)) in e.body.iter().zip(&t.body).enumerate() {
            if en != tn {
                return format!("block {} instruction {index}", e.id);
            }
        }
    }
    if expected.value_names != target.value_names {
        return "value names".to_string();
    }
    "function attributes".to_string()
}

// ---------------------------------------------------------------------------
// Shared helpers (this module's own, independent of the mid-end's)
// ---------------------------------------------------------------------------

/// Where each value is defined: `None` for a block parameter, else the
/// instruction's (block position, index) and its result count.
fn definitions(func: &Function) -> HashMap<ValueId, Option<(usize, usize)>> {
    let mut defs = HashMap::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (value, _) in &block.params {
            defs.insert(*value, None);
        }
        for (ni, node) in block.body.iter().enumerate() {
            for result in &node.results {
                defs.insert(*result, Some((bi, ni)));
            }
        }
    }
    defs
}

/// One function's definitions, indexed once per check (a check looks values
/// up many times; a scan per lookup would make it quadratic).
pub struct Defs<'f> {
    params: HashMap<ValueId, &'f Ty>,
    sole: HashMap<ValueId, &'f Inst>,
}

impl<'f> Defs<'f> {
    /// Index `func`: block parameters, and every instruction with exactly one
    /// result (the first definition wins where a malformed function has two).
    pub fn of(func: &'f Function) -> Self {
        let mut params = HashMap::new();
        let mut sole = HashMap::new();
        for block in &func.blocks {
            for (value, ty) in &block.params {
                params.entry(*value).or_insert(ty);
            }
            for node in &block.body {
                if let [result] = node.results.as_slice() {
                    sole.entry(*result).or_insert(&node.inst);
                }
            }
        }
        Self { params, sole }
    }

    /// The instruction defining `value` as its ONLY result.
    fn inst(&self, value: ValueId) -> Option<&'f Inst> {
        self.sole.get(&value).copied()
    }

    /// The type of `value`, for the value forms whose type this module reads
    /// directly: block parameters and single-result instructions whose result
    /// type is a field of the instruction. `None` for every other form, which
    /// a check needing the type then refuses.
    pub fn value_type(&self, value: ValueId) -> Option<Ty> {
        if let Some(ty) = self.params.get(&value) {
            return Some((*ty).clone());
        }
        match self.inst(value)? {
            Inst::Copy { ty, .. }
            | Inst::Load { ty, .. }
            | Inst::Const { ty, .. }
            | Inst::Select { ty, .. }
            | Inst::Undef { ty }
            | Inst::BinOp { ty, .. }
            | Inst::UnOp { ty, .. } => Some(ty.clone()),
            Inst::Cast { dst_ty, .. } => Some(dst_ty.clone()),
            Inst::ICmp { .. } | Inst::FCmp { .. } => Some(Ty::Bool),
            Inst::Alloca { .. } | Inst::GEP { .. } | Inst::GlobalAddr { .. } | Inst::NullPtr => {
                Some(Ty::Ptr)
            }
            _ => None,
        }
    }
}

/// Integer shape `(bits, signed)` of `ty` at `pointer_bits`.
fn int_shape(ty: &Ty, pointer_bits: u32) -> Option<(u32, bool)> {
    Some(match ty {
        Ty::I8 => (8, true),
        Ty::I16 => (16, true),
        Ty::I32 => (32, true),
        Ty::I64 => (64, true),
        Ty::I128 => (128, true),
        Ty::U8 => (8, false),
        Ty::U16 => (16, false),
        Ty::U32 => (32, false),
        Ty::U64 => (64, false),
        Ty::U128 => (128, false),
        Ty::Isize => (pointer_bits, true),
        Ty::Usize => (pointer_bits, false),
        _ => return None,
    })
}

/// Whether `value` is representable in `(bits, signed)` without wrapping.
fn fits(value: i128, bits: u32, signed: bool) -> bool {
    if bits >= 128 {
        return signed || value >= 0;
    }
    if signed {
        let half = 1i128 << (bits - 1);
        (-half..half).contains(&value)
    } else {
        value >= 0 && value < (1i128 << bits)
    }
}

/// Each block's position in `func.blocks`.
fn block_positions(func: &Function) -> HashMap<BlockId, usize> {
    func.blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id, i))
        .collect()
}

/// Drop the names of `removed` values (debug metadata must name only defined
/// values; trust-ir's validator refuses a dangling name).
fn drop_names(func: &mut Function, removed: &HashSet<ValueId>) {
    if let Some(names) = &mut func.value_names {
        names.retain(|(value, _)| !removed.contains(value));
    }
}

/// Every value an instruction of `func` uses.
fn used_values(func: &Function) -> HashSet<ValueId> {
    let mut used = HashSet::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        node.inst.visit_value_operands(|v| {
            used.insert(v);
        });
    }
    used
}

// ---------------------------------------------------------------------------
// Copy propagation
// ---------------------------------------------------------------------------

fn rebuild_copy_prop(
    _module: &Module,
    source: &Function,
    witness: &CopyPropWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let mut map: HashMap<ValueId, ValueId> = HashMap::new();
    for forward in &witness.forwards {
        if map.insert(forward.copy, forward.root).is_some() || forward.copy == forward.root {
            return Err(MidTvError::InconsistentForwarding {
                value: forward.copy,
            });
        }
    }
    let defs = Defs::of(source);
    for forward in &witness.forwards {
        if map.contains_key(&forward.root) {
            return Err(MidTvError::InconsistentForwarding {
                value: forward.root,
            });
        }
        let Some(Inst::Copy { ty, operand }) = defs.inst(forward.copy) else {
            return Err(MidTvError::NoDefinition {
                value: forward.copy,
                expected: "a single-result copy",
            });
        };
        let reaches = *operand == forward.root || map.get(operand) == Some(&forward.root);
        if !reaches {
            return Err(MidTvError::WrongRoot {
                copy: forward.copy,
                root: forward.root,
            });
        }
        if defs.value_type(forward.root).as_ref() != Some(ty) {
            return Err(MidTvError::TypeChange { copy: forward.copy });
        }
    }
    let removed: HashSet<ValueId> = map.keys().copied().collect();
    let mut expected = source.clone();
    for block in &mut expected.blocks {
        block
            .body
            .retain(|n| !(n.results.len() == 1 && removed.contains(&n.results[0])));
        for node in &mut block.body {
            trust_ir::mem2reg::rewrite_inst(&mut node.inst, &map);
        }
    }
    drop_names(&mut expected, &removed);
    Ok((
        expected,
        WitnessVerdict {
            exact: witness.forwards.len(),
            refinements: 0,
        },
    ))
}

// ---------------------------------------------------------------------------
// Pure dead-code elimination
// ---------------------------------------------------------------------------

/// How many `gep`s, `ptrtoptr`s and copies [`removal_class`] follows from a
/// pointer back to the allocation or global it is computed from.
const ROOT_DEPTH: usize = 64;

/// This module's removable table: the class of removing `inst` when its
/// results are unused, or `None` when it is not removable. The table is an
/// ALLOWLIST: an instruction form not named here is never removable.
/// The element count of `alloca T, count`: 1 without a count, `k` for an
/// integer constant `k >= 1` (the interpreter allocates `size(T) * k` bytes
/// and refuses a count below 1); `None` for any other count.
fn alloca_count(index: &Defs<'_>, count: Option<ValueId>) -> Option<u64> {
    let Some(count) = count else {
        return Some(1);
    };
    match index.inst(count)? {
        Inst::Const {
            ty,
            value: Constant::Int(k),
        } if ty.is_integer() => u64::try_from(*k).ok().filter(|&k| k >= 1),
        _ => None,
    }
}

pub fn removal_class(defs: &Defs<'_>, inst: &Inst) -> Option<RemovalClass> {
    let constant = |value: ValueId| matches!(defs.inst(value), Some(Inst::Const { .. }));
    // Whether `value` is a fresh frame allocation or a global's address, or a
    // pointer computed from one by `gep`s by constants, `ptrtoptr`s and
    // copies: an address whose bits no input chooses.
    let base = |value: ValueId| {
        let mut value = value;
        for _ in 0..ROOT_DEPTH {
            match defs.inst(value) {
                Some(Inst::Alloca { count, .. }) => return alloca_count(defs, *count).is_some(),
                Some(Inst::GlobalAddr { .. }) => return true,
                Some(Inst::GEP { base, indices, .. })
                    if indices.iter().all(|index| constant(*index)) =>
                {
                    value = *base;
                }
                Some(
                    Inst::Cast {
                        op: CastOp::PtrToPtr,
                        operand,
                        ..
                    }
                    | Inst::Copy { operand, .. },
                ) => value = *operand,
                _ => return false,
            }
        }
        false
    };
    let typed = |value: ValueId, ty: &Ty| defs.value_type(value).as_ref() == Some(ty);
    match inst {
        Inst::Const { .. } | Inst::NullPtr | Inst::GlobalAddr { .. } | Inst::Undef { .. } => {
            Some(RemovalClass::Exact)
        }
        // A copy of a value of its own type is the identity; a copy whose
        // operand has another type is a type error in the interpreter.
        Inst::Copy { ty, operand } => Some(if typed(*operand, ty) {
            RemovalClass::Exact
        } else {
            RemovalClass::Refinement
        }),
        // A shift by a constant amount below its fixed width, an unsigned
        // division or remainder by a nonzero constant, and a signed one by a
        // constant other than 0 and -1 are total on defined operands (the
        // constant read as the bits it holds at the width): the lane's
        // capture analysis reads an amount or a divisor, not the shifted or
        // divided value, as exposing an address.
        Inst::BinOp { op, ty, rhs, .. }
            if ty.is_integer()
                && !matches!(ty, Ty::Isize | Ty::Usize)
                && ty.bit_width().is_some_and(|bits| {
                    let Some(Inst::Const {
                        value: Constant::Int(k),
                        ty: kt,
                    }) = defs.inst(*rhs)
                    else {
                        return false;
                    };
                    if kt.bit_width() != Some(bits) {
                        return false;
                    }
                    let all = if bits >= 128 {
                        u128::MAX
                    } else {
                        (1u128 << bits) - 1
                    };
                    let k = (*k as u128) & all;
                    match op {
                        BinOp::Shl | BinOp::LShr | BinOp::AShr => k < u128::from(bits),
                        BinOp::UDiv | BinOp::URem => k != 0,
                        BinOp::SDiv | BinOp::SRem => k != 0 && k != all,
                        _ => false,
                    }
                }) =>
        {
            Some(RemovalClass::Refinement)
        }
        // Division, remainder and shifts are undefined for some operand VALUES
        // (a zero divisor, an out-of-range amount): past one, execution knows
        // something about its operands, which may be an address's bits.
        Inst::BinOp { op, .. }
            if !matches!(
                op,
                BinOp::UDiv
                    | BinOp::SDiv
                    | BinOp::URem
                    | BinOp::SRem
                    | BinOp::Shl
                    | BinOp::LShr
                    | BinOp::AShr
            ) =>
        {
            Some(RemovalClass::Refinement)
        }
        // A conversion defined only on some values (a float out of an
        // integer's range, an integer past the address space, a value that is
        // not a `bool` or `char`) is excluded for the same reason. An
        // `inttoptr` from an integer no wider than a wasm32 address is total
        // on a defined operand.
        Inst::Cast {
            op: CastOp::IntToPtr,
            src_ty,
            dst_ty,
            ..
        } if !matches!(dst_ty, Ty::Bool | Ty::Char)
            && (matches!(src_ty, Ty::Isize | Ty::Usize)
                || (src_ty.is_integer() && src_ty.bit_width().is_some_and(|w| w <= 32))) =>
        {
            Some(RemovalClass::Refinement)
        }
        Inst::Cast { op, dst_ty, .. }
            if !matches!(
                op,
                CastOp::FPToUI | CastOp::FPToSI | CastOp::IntToPtr | CastOp::Transmute
            ) && !matches!(dst_ty, Ty::Bool | Ty::Char) =>
        {
            Some(RemovalClass::Refinement)
        }
        Inst::UnOp { .. }
        | Inst::Overflow { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Select { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::MakeAggregate { .. }
        | Inst::ArraySplat { .. }
        | Inst::Alloca { count: None, .. } => Some(RemovalClass::Refinement),
        Inst::Alloca {
            count: Some(count), ..
        } if alloca_count(defs, Some(*count)).is_some() => Some(RemovalClass::Refinement),
        // Field access over a value of its own aggregate type. The rustc bridge
        // also writes `extractfield`/`insertfield` over a POINTER to the
        // aggregate, which the wasm lane lowers as a load or a store through
        // it; that form, or an operand of unknown type, stays.
        Inst::ExtractField { ty, aggregate, .. } | Inst::InsertField { ty, aggregate, .. }
            if typed(*aggregate, ty) =>
        {
            Some(RemovalClass::Refinement)
        }
        // An access or address computation only from a fresh allocation or a
        // global by constant indices: whether it is defined does not depend on
        // any input's bits.
        Inst::Load {
            volatile: false,
            ptr,
            ..
        } if base(*ptr) => Some(RemovalClass::Refinement),
        Inst::GEP {
            base: b, indices, ..
        } if base(*b) && indices.iter().all(|index| constant(*index)) => {
            Some(RemovalClass::Refinement)
        }
        _ => None,
    }
}

fn rebuild_dce(
    _module: &Module,
    source: &Function,
    witness: &DceWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let defs = Defs::of(source);
    let positions = block_positions(source);
    let mut verdict = WitnessVerdict::default();
    let mut doomed: HashSet<(BlockId, usize)> = HashSet::new();
    let mut removed: HashSet<ValueId> = HashSet::new();
    for removal in &witness.removals {
        let node = positions
            .get(&removal.block)
            .and_then(|&bi| source.blocks[bi].body.get(removal.index))
            .ok_or(MidTvError::NoInstruction {
                block: removal.block,
                index: removal.index,
            })?;
        if node.results != removal.results || !doomed.insert((removal.block, removal.index)) {
            return Err(MidTvError::NoInstruction {
                block: removal.block,
                index: removal.index,
            });
        }
        let derived = removal_class(&defs, &node.inst).ok_or(MidTvError::Effectful {
            block: removal.block,
            index: removal.index,
        })?;
        if derived != removal.class {
            return Err(MidTvError::WrongClass {
                block: removal.block,
                index: removal.index,
                claimed: removal.class,
                derived,
            });
        }
        match derived {
            RemovalClass::Exact => verdict.exact += 1,
            RemovalClass::Refinement => verdict.refinements += 1,
        }
        removed.extend(node.results.iter().copied());
    }
    let mut expected = source.clone();
    for block in &mut expected.blocks {
        let id = block.id;
        let mut index = 0usize;
        block.body.retain(|_| {
            let keep = !doomed.contains(&(id, index));
            index += 1;
            keep
        });
    }
    if let Some(value) = used_values(&expected).intersection(&removed).next() {
        return Err(MidTvError::RemovedValueUsed { value: *value });
    }
    drop_names(&mut expected, &removed);
    Ok((expected, verdict))
}

// ---------------------------------------------------------------------------
// Constant-branch folding
// ---------------------------------------------------------------------------

/// The edge (target, arguments) the terminator of `block` takes, when it
/// branches on a constant this module can evaluate.
fn constant_edge(
    defs: &Defs<'_>,
    pointer_bits: u32,
    inst: &Inst,
) -> Option<(BlockId, Vec<ValueId>)> {
    match inst {
        Inst::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        } => match defs.inst(*cond)? {
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(true),
            } => Some((*then_target, then_args.clone())),
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(false),
            } => Some((*else_target, else_args.clone())),
            _ => None,
        },
        Inst::Switch {
            value,
            default,
            default_args,
            cases,
            exhaustive_enum_unreachable,
        } => {
            let Inst::Const {
                ty,
                value: Constant::Int(scrutinee),
            } = defs.inst(*value)?
            else {
                return None;
            };
            let (bits, signed) = int_shape(ty, pointer_bits)?;
            if !fits(*scrutinee, bits, signed) {
                return None;
            }
            let mut taken = None;
            for case in cases {
                let Constant::Int(c) = case.value else {
                    return None;
                };
                if !fits(c, bits, signed) {
                    return None;
                }
                if taken.is_none() && c == *scrutinee {
                    taken = Some((case.target, case.args.clone()));
                }
            }
            match taken {
                Some(edge) => Some(edge),
                None if *exhaustive_enum_unreachable => None,
                None => Some((*default, default_args.clone())),
            }
        }
        _ => None,
    }
}

/// Blocks reachable from the entry, by this module's own walk.
fn reachable(func: &Function) -> BTreeSet<BlockId> {
    let positions = block_positions(func);
    let mut seen = BTreeSet::new();
    let mut stack = vec![func.entry];
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        if let Some(&bi) = positions.get(&id)
            && let Some(last) = func.blocks[bi].body.last()
        {
            for edge in last.inst.successor_edges() {
                stack.push(edge.target);
            }
        }
    }
    seen
}

fn rebuild_branch_fold(
    source: &Function,
    pointer_bits: u32,
    witness: &BranchFoldWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let defs = Defs::of(source);
    let positions = block_positions(source);
    let mut expected = source.clone();
    let mut folded = HashSet::new();
    for fold in &witness.folds {
        if !folded.insert(fold.block) {
            return Err(MidTvError::NotConstantBranch { block: fold.block });
        }
        let Some(&bi) = positions.get(&fold.block) else {
            return Err(MidTvError::NotConstantBranch { block: fold.block });
        };
        let block = &mut expected.blocks[bi];
        let Some(last) = block.body.last_mut() else {
            return Err(MidTvError::NotConstantBranch { block: fold.block });
        };
        let (target, args) = constant_edge(&defs, pointer_bits, &last.inst)
            .ok_or(MidTvError::NotConstantBranch { block: fold.block })?;
        if target != fold.target {
            return Err(MidTvError::WrongTarget {
                block: fold.block,
                claimed: fold.target,
                derived: target,
            });
        }
        last.inst = Inst::Br { target, args };
    }
    let live = reachable(&expected);
    let doomed: HashSet<BlockId> = witness.removed_blocks.iter().copied().collect();
    if doomed.len() != witness.removed_blocks.len() {
        return Err(MidTvError::TargetDiffers {
            detail: "a block is removed twice".to_string(),
        });
    }
    let mut removed_values = HashSet::new();
    for id in &doomed {
        if live.contains(id) || *id == expected.entry {
            return Err(MidTvError::ReachableBlockRemoved { block: *id });
        }
        let Some(&bi) = positions.get(id) else {
            return Err(MidTvError::ReachableBlockRemoved { block: *id });
        };
        let block = &expected.blocks[bi];
        removed_values.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            removed_values.extend(node.results.iter().copied());
        }
    }
    expected.blocks.retain(|b| !doomed.contains(&b.id));
    if let Some(value) = used_values(&expected).intersection(&removed_values).next() {
        return Err(MidTvError::RemovedValueUsed { value: *value });
    }
    drop_names(&mut expected, &removed_values);
    Ok((
        expected,
        WitnessVerdict {
            exact: witness.folds.len() + witness.removed_blocks.len(),
            refinements: 0,
        },
    ))
}

// ---------------------------------------------------------------------------
// Pointer chain -> byte-offset GEP
// ---------------------------------------------------------------------------

/// The steps a provenance or constant walk takes before refusing.
const MAX_CHAIN: usize = 64;

/// `(size, displacement)` of the `alloca` `v` lies in (count-free, or
/// counted by an integer constant `k >= 1`: `size(T) * k` bytes), when `v`
/// is the `alloca` or is derived from it by copies, `ptrtoptr`s and `gep`s
/// by non-negative integer constants (the interpreter's flat GEP:
/// `size(pointee) * sum(indices)` bytes on), every step strictly inside the
/// allocation. Such a value is `(A, d)` with `d < size(A)` on every
/// execution, `A` the latest allocation of that `alloca`.
fn alloca_displacement(
    layout: &FsymLayout<'_>,
    index: &Defs<'_>,
    mut v: ValueId,
) -> Result<(u64, u64), &'static str> {
    let mut disp: u64 = 0;
    for _ in 0..MAX_CHAIN {
        match index.inst(v) {
            Some(Inst::Alloca { ty, count, .. }) => {
                let count = alloca_count(index, *count)
                    .ok_or("the allocation's count is not a positive constant")?;
                let size = layout
                    .size(ty)
                    .ok()
                    .and_then(|s| s.checked_mul(count))
                    .ok_or("the allocation has no byte size")?;
                if size == 0 || disp >= size {
                    return Err("the base is not inside its allocation");
                }
                return Ok((size, disp));
            }
            Some(
                Inst::Copy { operand, .. }
                | Inst::Cast {
                    op: CastOp::PtrToPtr,
                    operand,
                    ..
                },
            ) => v = *operand,
            Some(Inst::GEP {
                pointee_ty,
                base,
                indices,
                ..
            }) => {
                let elem = layout
                    .size(pointee_ty)
                    .map_err(|_| "a gep element has no byte size")?;
                for k in indices {
                    let Some(Inst::Const {
                        ty,
                        value: Constant::Int(k),
                    }) = index.inst(*k)
                    else {
                        return Err("the base is offset by a non-constant");
                    };
                    if !ty.is_integer() {
                        return Err("the base is offset by a non-integer");
                    }
                    let k = u64::try_from(*k).map_err(|_| "the base is offset backward")?;
                    disp = elem
                        .checked_mul(k)
                        .and_then(|d| disp.checked_add(d))
                        .ok_or("the base's offset overflows")?;
                }
                v = *base;
            }
            _ => return Err("the base is not derived from a fresh allocation"),
        }
    }
    Err("the base's derivation is too long")
}

/// The value of the constant expression `v` at the integer width `bits`: an
/// integer constant of that width, the same-width `bitcast` of one, or an
/// `add` or `mul` of two such, each in `[0, 2^(bits - 1))`, so the value
/// does not depend on signedness or on wrapping.
fn constant_expression(index: &Defs<'_>, v: ValueId, bits: u32, pointer_bits: u32) -> Option<u64> {
    fn eval(
        index: &Defs<'_>,
        v: ValueId,
        bits: u32,
        pointer_bits: u32,
        depth: usize,
    ) -> Option<i128> {
        if depth > MAX_CHAIN {
            return None;
        }
        let width = |ty: &Ty| int_shape(ty, pointer_bits).map(|(b, _)| b);
        let bound: i128 = 1i128 << (bits - 1);
        let value = match index.inst(v)? {
            Inst::Const {
                ty,
                value: Constant::Int(k),
            } if width(ty) == Some(bits) => *k,
            Inst::Cast {
                op: CastOp::Bitcast,
                src_ty,
                dst_ty,
                operand,
            } if width(src_ty) == Some(bits) && width(dst_ty) == Some(bits) => {
                match index.inst(*operand)? {
                    Inst::Const {
                        ty,
                        value: Constant::Int(k),
                    } if ty == src_ty => *k,
                    _ => return None,
                }
            }
            Inst::BinOp { op, ty, lhs, rhs } if width(ty) == Some(bits) => {
                let l = eval(index, *lhs, bits, pointer_bits, depth + 1)?;
                let r = eval(index, *rhs, bits, pointer_bits, depth + 1)?;
                match op {
                    BinOp::Add => l.checked_add(r)?,
                    BinOp::Mul => l.checked_mul(r)?,
                    _ => return None,
                }
            }
            _ => return None,
        };
        (0..bound).contains(&value).then_some(value)
    }
    if bits == 0 || bits > 64 {
        return None;
    }
    u64::try_from(eval(index, v, bits, pointer_bits, 0)?).ok()
}

fn rebuild_ptr_gep(
    module: &Module,
    pointer_bits: u32,
    source: &Function,
    witness: &PtrGepWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let defs = definitions(source);
    let index = Defs::of(source);
    let layout = FsymLayout::new(module);
    let mut expected = source.clone();
    let mut seen = HashSet::new();
    let mut used: HashSet<ValueId> = HashSet::new();
    for node in source.blocks.iter().flat_map(|b| &b.body) {
        node.inst.visit_value_operands(|v| {
            used.insert(v);
        });
    }
    let mut fresh: HashSet<ValueId> = HashSet::new();
    let mut replaced: HashMap<(usize, usize), Vec<trust_ir::InstrNode>> = HashMap::new();
    for rewrite in &witness.rewrites {
        let value = rewrite.result;
        let bad = |why| MidTvError::NotPointerChain { value, why };
        if !seen.insert(value) {
            return Err(bad("rewritten twice"));
        }
        let (bi, ni) = match defs.get(&value) {
            Some(Some(at)) => *at,
            _ => return Err(bad("no defining instruction")),
        };
        let block = &source.blocks[bi];
        if block.id != rewrite.block || ni != rewrite.index || block.body[ni].results != [value] {
            return Err(bad("the instruction is not at the claimed position"));
        }
        let Inst::Cast {
            op: CastOp::IntToPtr,
            src_ty: int_ty,
            dst_ty: Ty::Ptr,
            operand: sum,
        } = &block.body[ni].inst
        else {
            return Err(bad("not an inttoptr to ptr"));
        };
        let (bits, _) = int_shape(int_ty, pointer_bits).ok_or(bad("not an integer"))?;
        if bits < pointer_bits {
            return Err(bad("the integer is narrower than a pointer"));
        }
        let is_base = |v: ValueId| {
            matches!(
                index.inst(v),
                Some(Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: Ty::Ptr,
                    dst_ty,
                    operand,
                }) if dst_ty == int_ty && *operand == rewrite.base
            )
        };
        // The round trip `inttoptr(ptrtoint(base))` names its integer as the
        // offset operand; otherwise the address is `base` plus a constant
        // expression of the integer's type.
        let offset_value = if is_base(*sum) {
            if rewrite.offset != 0 || rewrite.offset_value != *sum {
                return Err(bad("a round trip's offset is not zero"));
            }
            *sum
        } else {
            let Some(Inst::BinOp {
                op: BinOp::Add,
                ty: add_ty,
                lhs,
                rhs,
            }) = index.inst(*sum)
            else {
                return Err(bad("the address is not an add"));
            };
            if add_ty != int_ty {
                return Err(bad("the add has another type"));
            }
            let offset_value = if is_base(*lhs) {
                *rhs
            } else if is_base(*rhs) {
                *lhs
            } else {
                return Err(bad("neither addend is ptrtoint of the base"));
            };
            if offset_value != rewrite.offset_value {
                return Err(bad("the offset operand differs"));
            }
            if index.value_type(offset_value).as_ref() != Some(int_ty) {
                return Err(bad("the offset is not of the address's integer type"));
            }
            let k = constant_expression(&index, offset_value, bits, pointer_bits)
                .ok_or(bad("the offset is not a non-negative constant expression"))?;
            if k != rewrite.offset {
                return Err(bad("the offset constant differs"));
            }
            offset_value
        };
        // `copy ptr base` and `gep u8, base` read the base as a `ptr`.
        if index.value_type(rewrite.base) != Some(Ty::Ptr) {
            return Err(bad("the base is not a ptr"));
        }
        let (size, disp) = alloca_displacement(&layout, &index, rewrite.base).map_err(bad)?;
        if disp
            .checked_add(rewrite.offset)
            .is_none_or(|end| end >= size)
        {
            return Err(MidTvError::OffsetOutOfBounds {
                value,
                offset: disp.saturating_add(rewrite.offset),
                size,
            });
        }
        let mut node = block.body[ni].clone();
        let mut nodes = Vec::new();
        node.inst = match (rewrite.offset, rewrite.folded) {
            (0, None) => Inst::Copy {
                ty: Ty::Ptr,
                operand: rewrite.base,
            },
            (0, Some(_)) => return Err(bad("a zero offset is folded")),
            (_, None) => Inst::GEP {
                pointee_ty: Ty::U8,
                base: rewrite.base,
                indices: vec![offset_value],
                inbounds: true,
            },
            (offset, Some(folded)) => {
                if defs.contains_key(&folded) || used.contains(&folded) || !fresh.insert(folded) {
                    return Err(bad("the folded offset is not a fresh value"));
                }
                let mut constant = node.clone();
                constant.inst = Inst::Const {
                    ty: int_ty.clone(),
                    value: Constant::Int(i128::from(offset)),
                };
                constant.results = vec![folded];
                nodes.push(constant);
                Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: rewrite.base,
                    indices: vec![folded],
                    inbounds: true,
                }
            }
        };
        nodes.push(node);
        replaced.insert((bi, ni), nodes);
    }
    for (bi, block) in expected.blocks.iter_mut().enumerate() {
        let body = std::mem::take(&mut block.body);
        block.body = body
            .into_iter()
            .enumerate()
            .flat_map(|(ni, node)| replaced.remove(&(bi, ni)).unwrap_or_else(|| vec![node]))
            .collect();
    }
    Ok((
        expected,
        WitnessVerdict {
            exact: witness.rewrites.len(),
            refinements: 0,
        },
    ))
}

// ---------------------------------------------------------------------------
// Memory slots: the facts the memory checkers share
// ---------------------------------------------------------------------------

/// The uses of each value: `(block position, node index)`, once per node.
fn use_positions(func: &Function) -> HashMap<ValueId, Vec<(usize, usize)>> {
    let mut uses: HashMap<ValueId, Vec<(usize, usize)>> = HashMap::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            node.inst.visit_value_operands(|v| {
                let list = uses.entry(v).or_default();
                if list.last() != Some(&(bi, ni)) {
                    list.push((bi, ni));
                }
            });
        }
    }
    uses
}

/// Every incoming edge of each block, by position: one entry per edge (a
/// terminator naming a block twice gives it two), unwind edges included.
fn incoming_edges(func: &Function, positions: &HashMap<BlockId, usize>) -> Vec<Vec<usize>> {
    let mut preds = vec![Vec::new(); func.blocks.len()];
    for (bi, block) in func.blocks.iter().enumerate() {
        if let Some(last) = block.body.last() {
            for edge in last.inst.successor_edges() {
                if let Some(&ti) = positions.get(&edge.target) {
                    preds[ti].push(bi);
                }
            }
        }
    }
    preds
}

/// The scalar types whose value a load returns exactly as a store of the
/// same type wrote it in the reference interpreter (`encode_image` /
/// `decode_leaf`: integers, `bool`, `char` and floats are their bytes). A
/// pointer is NOT one: a reload resolves the stored address to whichever live
/// allocation contains it (`resolve_pointer_kind`), which for a one-past-the-
/// end or dangling pointer may be another allocation than the stored value's.
fn round_trips(ty: &Ty) -> bool {
    matches!(
        ty,
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
            | Ty::Bool
            | Ty::Char
            | Ty::F16
            | Ty::F32
            | Ty::F64
    )
}

/// One load or store through a slot family's pointers.
#[derive(Debug, Clone)]
struct SlotAccess {
    at: (usize, usize),
    store: bool,
}

/// A count-free `alloca` whose address is unobservable: every use of it is
/// a plain load or store through it, or a `gep` of it by one constant byte
/// offset whose every use is a plain load or store through it. `pointers`
/// maps each of those pointers to its byte offset; `stores` indexes the
/// stores among `accesses` by block, as (node, offset, size).
#[derive(Debug, Clone)]
struct SlotFamily {
    at: (usize, usize),
    pointers: HashMap<ValueId, u64>,
    accesses: Vec<SlotAccess>,
    stores: HashMap<usize, Vec<(usize, u64, u64)>>,
}

/// The family of `alloca` in `source` (see [`SlotFamily`]), derived from the
/// source alone with the interpreter's layout ([`FsymLayout`]), or why it is
/// not one. No other value can reach the allocation: its address never
/// leaves these pointers (no `ptrtoint`, no call, no store of it, no block
/// argument), and an address whose bits are never observed cannot be rebuilt
/// (the premise of the capture analysis, `trust_cg_irmid::escape`).
fn slot_family(
    module: &Module,
    source: &Function,
    uses: &HashMap<ValueId, Vec<(usize, usize)>>,
    defs: &HashMap<ValueId, Option<(usize, usize)>>,
    alloca: ValueId,
) -> Result<SlotFamily, &'static str> {
    let layout = FsymLayout::new(module);
    let at = match defs.get(&alloca) {
        Some(Some(at)) => *at,
        _ => return Err("not defined by an instruction"),
    };
    let node = &source.blocks[at.0].body[at.1];
    let Inst::Alloca {
        ty, count: None, ..
    } = &node.inst
    else {
        return Err("not a count-free alloca");
    };
    if node.results != [alloca] {
        return Err("not a count-free alloca");
    }
    let size = layout
        .size(ty)
        .map_err(|_| "the allocation has no layout")?;
    if size == 0 {
        return Err("the allocation is empty");
    }
    let mut family = SlotFamily {
        at,
        pointers: HashMap::from([(alloca, 0)]),
        accesses: Vec::new(),
        stores: HashMap::new(),
    };
    let index = Defs::of(source);
    let mut pending = vec![alloca];
    while let Some(pointer) = pending.pop() {
        let offset = family.pointers[&pointer];
        for &(bi, ni) in uses.get(&pointer).map_or(&[][..], Vec::as_slice) {
            let node = &source.blocks[bi].body[ni];
            let access = match &node.inst {
                Inst::Load {
                    ty,
                    ptr,
                    volatile: false,
                    ..
                } if *ptr == pointer => Some((false, ty)),
                Inst::Store {
                    ty,
                    ptr,
                    value,
                    volatile: false,
                    ..
                } if *ptr == pointer && !family.pointers.contains_key(value) => Some((true, ty)),
                Inst::GEP {
                    pointee_ty: Ty::U8 | Ty::I8,
                    base,
                    indices,
                    ..
                } if pointer == alloca && *base == alloca => {
                    let [k] = indices.as_slice() else {
                        return Err("the address is offset by more than one index");
                    };
                    let Some(Inst::Const {
                        ty: k_ty,
                        value: Constant::Int(k),
                    }) = index.inst(*k)
                    else {
                        return Err("the address is offset by a non-constant amount");
                    };
                    let k = u64::try_from(*k).map_err(|_| "the address is offset backwards")?;
                    if !k_ty.is_integer() && !matches!(k_ty, Ty::Isize | Ty::Usize) {
                        return Err("the address is offset by a non-integer");
                    }
                    if k >= size {
                        return Err("the address is offset outside the allocation");
                    }
                    let [g] = node.results.as_slice() else {
                        return Err("the offset address is not one value");
                    };
                    if family.pointers.insert(*g, k).is_none() {
                        pending.push(*g);
                    }
                    None
                }
                _ => return Err("the address is used other than by a plain load or store"),
            };
            if let Some((store, ty)) = access {
                let width = layout.size(ty).map_err(|_| "an access has no layout")?;
                let end = offset.checked_add(width).ok_or("an access overflows")?;
                if width == 0 || end > size {
                    return Err("an access leaves the allocation");
                }
                if store {
                    family
                        .stores
                        .entry(bi)
                        .or_default()
                        .push((ni, offset, width));
                }
                family.accesses.push(SlotAccess {
                    at: (bi, ni),
                    store,
                });
            }
        }
    }
    Ok(family)
}

/// Whether `[a, a + an)` and `[b, b + bn)` share a byte.
fn overlaps(a: u64, an: u64, b: u64, bn: u64) -> bool {
    a < b.saturating_add(bn) && b < a.saturating_add(an)
}

/// The question [`sole_reaching_store`] answers: whether the store at
/// `store`, of `value`, is the last write of `[offset, offset + size)` through
/// the family of the allocation at `alloca`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ReachKey {
    alloca: (usize, usize),
    store: (usize, usize),
    value: ValueId,
    offset: u64,
    size: u64,
}

/// A node's verdict for a [`ReachKey`]: `Ok` the store, `Err` another event.
type ReachEvent = (usize, Result<(), &'static str>);

/// What the walks for one [`ReachKey`] have established.
#[derive(Debug, Default)]
struct ReachState {
    /// Per block reached, its event nodes for the key in node order.
    events: HashMap<usize, Vec<ReachEvent>>,
    /// Blocks proven from their end: every backward path from the end of
    /// each meets the store before any other event. After a walk succeeds
    /// the set is closed: each member's last event is the store, or it has
    /// no event, is not the entry, does not take the value as a parameter,
    /// has predecessors, and every predecessor is a member. A union of
    /// closed sets is closed, so a later walk may stop at any member; a
    /// failed walk discards the key's state.
    proven: HashSet<usize>,
}

/// The walks of one store-forwarding check, shared across its forwards: each
/// block's events are collected at most once per key, so a check's cost is
/// bounded by its keys times the function's size, not by its forwards.
#[derive(Debug, Default)]
struct ReachProofs {
    states: HashMap<ReachKey, ReachState>,
    /// Blocks whose events were collected, over all keys.
    block_scans: usize,
    /// Blocks a walk entered from their end, over all keys.
    block_visits: usize,
}

/// The event nodes of block `bi` for `key`, in node order: the store, the
/// allocation, a definition of the value, and a family store overlapping the
/// key's bytes. At one node the first of those, in that order, decides.
fn block_events(
    family: &SlotFamily,
    value_defs: &HashMap<ValueId, Vec<(usize, usize)>>,
    key: &ReachKey,
    bi: usize,
) -> Vec<ReachEvent> {
    let mut events: Vec<(usize, u8, Result<(), &'static str>)> = Vec::new();
    if key.store.0 == bi {
        events.push((key.store.1, 0, Ok(())));
    }
    if family.at.0 == bi {
        events.push((
            family.at.1,
            1,
            Err("the allocation is renewed on a path to the load (an undefined read)"),
        ));
    }
    for &(db, dn) in value_defs.get(&key.value).map_or(&[][..], Vec::as_slice) {
        if db == bi {
            events.push((
                dn,
                2,
                Err("the stored value is redefined on a path to the load"),
            ));
        }
    }
    for &(ni, offset, size) in family.stores.get(&bi).map_or(&[][..], Vec::as_slice) {
        if overlaps(offset, size, key.offset, key.size) {
            events.push((ni, 3, Err("another store to the slot intervenes")));
        }
    }
    events.sort_by_key(|&(ni, rank, _)| (ni, rank));
    events.dedup_by_key(|event| event.0);
    events
        .into_iter()
        .map(|(ni, _, verdict)| (ni, verdict))
        .collect()
}

/// The events of block `bi` for `key`, collected on first use.
fn events_in<'s>(
    events: &'s mut HashMap<usize, Vec<ReachEvent>>,
    block_scans: &mut usize,
    family: &SlotFamily,
    value_defs: &HashMap<ValueId, Vec<(usize, usize)>>,
    key: &ReachKey,
    bi: usize,
) -> &'s [ReachEvent] {
    events.entry(bi).or_insert_with(|| {
        *block_scans += 1;
        block_events(family, value_defs, key, bi)
    })
}

/// Where each value is defined by an instruction, every definition listed
/// (a malformed function may define a value twice).
fn instruction_definitions(func: &Function) -> HashMap<ValueId, Vec<(usize, usize)>> {
    let mut defs: HashMap<ValueId, Vec<(usize, usize)>> = HashMap::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            for result in &node.results {
                defs.entry(*result).or_default().push((bi, ni));
            }
        }
    }
    defs
}

/// Whether every path from the entry to the node at `load` executes the
/// store `key.store` after the last execution of the allocation, of every
/// store through the family that overlaps the key's bytes, and of the
/// definition of `key.value`. Walks the CFG backward from `load` and fails on
/// the first other such event or on reaching the entry (or a block with no
/// predecessor); every CFG path is walked, feasible or not, so the answer is
/// conservative on any CFG, reducible or not. Blocks proven for the same key
/// by an earlier forward are not walked again (see [`ReachState`]).
#[allow(clippy::too_many_arguments)]
fn sole_reaching_store(
    source: &Function,
    preds: &[Vec<usize>],
    entry: usize,
    family: &SlotFamily,
    value_defs: &HashMap<ValueId, Vec<(usize, usize)>>,
    proofs: &mut ReachProofs,
    load: (usize, usize),
    key: ReachKey,
) -> Result<(), &'static str> {
    let at_start = |bi: usize, pending: &mut Vec<usize>| -> Result<(), &'static str> {
        if bi == entry {
            return Err("a path from the function entry reaches the load without the store");
        }
        if source.blocks[bi]
            .params
            .iter()
            .any(|(v, _)| *v == key.value)
        {
            return Err("the stored value is redefined on a path to the load");
        }
        if preds[bi].is_empty() {
            return Err("a block without predecessors reaches the load");
        }
        pending.extend(preds[bi].iter().copied());
        Ok(())
    };
    let ReachProofs {
        states,
        block_scans,
        block_visits,
    } = proofs;
    let outcome = {
        let ReachState { events, proven } = states.entry(key).or_default();
        let (lb, li) = load;
        let here = events_in(events, block_scans, family, value_defs, &key, lb);
        let before = here.partition_point(|&(ni, _)| ni < li);
        match before.checked_sub(1).map(|i| here[i].1) {
            Some(verdict) => verdict,
            None => (|| {
                let mut pending: Vec<usize> = Vec::new();
                at_start(lb, &mut pending)?;
                while let Some(bi) = pending.pop() {
                    if !proven.insert(bi) {
                        continue;
                    }
                    *block_visits += 1;
                    match events_in(events, block_scans, family, value_defs, &key, bi).last() {
                        Some(&(_, verdict)) => verdict?,
                        None => at_start(bi, &mut pending)?,
                    }
                }
                Ok(())
            })(),
        }
    };
    if outcome.is_err() {
        states.remove(&key);
    }
    outcome
}

/// The family of the slot `pointer` addresses (an `alloca` or a `gep` of
/// one), computed once per allocation.
fn family_of<'c>(
    cache: &'c mut HashMap<ValueId, Result<SlotFamily, &'static str>>,
    module: &Module,
    source: &Function,
    uses: &HashMap<ValueId, Vec<(usize, usize)>>,
    defs: &HashMap<ValueId, Option<(usize, usize)>>,
    index: &Defs<'_>,
    pointer: ValueId,
) -> Result<&'c SlotFamily, &'static str> {
    let root = match index.inst(pointer) {
        Some(Inst::Alloca { .. }) => pointer,
        Some(Inst::GEP { base, .. }) => *base,
        _ => return Err("the address is not an allocation or an offset of one"),
    };
    let family = cache
        .entry(root)
        .or_insert_with(|| slot_family(module, source, uses, defs, root));
    match family {
        Ok(family) if family.pointers.contains_key(&pointer) => Ok(family),
        Ok(_) => Err("the address is not an offset of the allocation"),
        Err(why) => Err(*why),
    }
}

// ---------------------------------------------------------------------------
// Single-dominating-store forwarding
// ---------------------------------------------------------------------------

fn rebuild_store_fwd(
    module: &Module,
    source: &Function,
    witness: &StoreFwdWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    rebuild_store_fwd_with(module, source, witness, &mut ReachProofs::default())
}

/// [`rebuild_store_fwd`] with its walks' state exposed (the cost regression
/// test reads [`ReachProofs::block_scans`]).
fn rebuild_store_fwd_with(
    module: &Module,
    source: &Function,
    witness: &StoreFwdWitness,
    proofs: &mut ReachProofs,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let defs = definitions(source);
    let index = Defs::of(source);
    let uses = use_positions(source);
    let positions = block_positions(source);
    let preds = incoming_edges(source, &positions);
    let entry = *positions
        .get(&source.entry)
        .ok_or(MidTvError::TargetDiffers {
            detail: "the source has no entry block".to_string(),
        })?;
    let value_defs = instruction_definitions(source);
    let mut families: HashMap<ValueId, Result<SlotFamily, &'static str>> = HashMap::new();
    let mut expected = source.clone();
    let mut seen = HashSet::new();
    for forward in &witness.forwards {
        let load_value = forward.result;
        let bad = |why| MidTvError::NotForwardable {
            load: load_value,
            why,
        };
        if !seen.insert(load_value) {
            return Err(bad("forwarded twice"));
        }
        let load_at = match defs.get(&load_value) {
            Some(Some(at)) => *at,
            _ => return Err(bad("no defining instruction")),
        };
        let load_node = &source.blocks[load_at.0].body[load_at.1];
        if source.blocks[load_at.0].id != forward.block
            || load_at.1 != forward.index
            || load_node.results != [load_value]
        {
            return Err(bad("the load is not at the claimed position"));
        }
        let Inst::Load {
            ty,
            ptr,
            volatile: false,
            align,
        } = &load_node.inst
        else {
            return Err(bad("not a plain load"));
        };
        let store_at = positions
            .get(&forward.store_block)
            .and_then(|&bi| {
                (forward.store_index < source.blocks[bi].body.len())
                    .then_some((bi, forward.store_index))
            })
            .ok_or(bad("no store at the claimed position"))?;
        let Inst::Store {
            ty: store_ty,
            ptr: store_ptr,
            value,
            volatile: false,
            align: store_align,
        } = &source.blocks[store_at.0].body[store_at.1].inst
        else {
            return Err(bad("the claimed store is not a plain store"));
        };
        if store_ty != ty || store_align != align {
            return Err(bad("the store's type or alignment differs from the load's"));
        }
        if *value != forward.value {
            return Err(bad("the forwarded value is not the stored one"));
        }
        if !round_trips(ty) {
            return Err(bad("a reload of this type is not the stored value"));
        }
        if matches!(index.inst(*value), Some(Inst::Undef { .. })) {
            return Err(bad("the stored value is poison"));
        }
        // `copy` of the value is the identity only at the value's own type: a
        // store may write a value of another type at its own (an enum a call
        // returns, stored as its tag byte).
        let value_ty = index
            .value_type(*value)
            .or_else(|| match index.inst(*value) {
                Some(Inst::Call { callee, .. }) => module
                    .function_by_id(*callee)
                    .and_then(|f| module.func_type(f.ty))
                    .and_then(|ft| match ft.returns.as_slice() {
                        [r] => Some(r.clone()),
                        _ => None,
                    }),
                _ => None,
            });
        if value_ty.as_ref() != Some(ty) {
            return Err(bad(
                "the stored value's type is not the load's (or is unknown)",
            ));
        }
        let family = family_of(&mut families, module, source, &uses, &defs, &index, *ptr)
            .map_err(|why| MidTvError::SlotObservable { slot: *ptr, why })?;
        if !family.pointers.contains_key(store_ptr) {
            return Err(bad("the store and the load address different allocations"));
        }
        let offset = family.pointers[ptr];
        if family.pointers[store_ptr] != offset {
            return Err(bad("the store and the load address different offsets"));
        }
        let width = FsymLayout::new(module)
            .size(ty)
            .map_err(|_| bad("the load has no layout"))?;
        let key = ReachKey {
            alloca: family.at,
            store: store_at,
            value: *value,
            offset,
            size: width,
        };
        sole_reaching_store(
            source,
            &preds,
            entry,
            family,
            &value_defs,
            proofs,
            load_at,
            key,
        )
        .map_err(|why| MidTvError::NoUniqueReachingStore {
            load: load_value,
            why,
        })?;
        expected.blocks[load_at.0].body[load_at.1].inst = Inst::Copy {
            ty: ty.clone(),
            operand: *value,
        };
    }
    Ok((
        expected,
        WitnessVerdict {
            exact: witness.forwards.len(),
            refinements: 0,
        },
    ))
}

// ---------------------------------------------------------------------------
// Dead slots
// ---------------------------------------------------------------------------

fn rebuild_dead_slot(
    module: &Module,
    source: &Function,
    witness: &DeadSlotWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let defs = definitions(source);
    let uses = use_positions(source);
    let positions = block_positions(source);
    let mut doomed: HashSet<(usize, usize)> = HashSet::new();
    let mut slots = HashSet::new();
    for slot in &witness.slots {
        let bad = |why| MidTvError::SlotObservable {
            slot: slot.alloca,
            why,
        };
        if !slots.insert(slot.alloca) {
            return Err(bad("the slot is claimed twice"));
        }
        let family = slot_family(module, source, &uses, &defs, slot.alloca).map_err(bad)?;
        if family.accesses.iter().any(|a| !a.store) {
            return Err(bad("the slot is read"));
        }
        let derived: BTreeSet<(usize, usize)> = family.accesses.iter().map(|a| a.at).collect();
        let mut claimed = BTreeSet::new();
        for (block, index) in &slot.stores {
            let at = positions
                .get(block)
                .map(|&bi| (bi, *index))
                .ok_or(bad("a claimed store is not in the function"))?;
            claimed.insert(at);
        }
        if claimed != derived || claimed.len() != slot.stores.len() {
            return Err(bad("the claimed stores are not the slot's stores"));
        }
        doomed.extend(derived);
    }
    let mut expected = source.clone();
    for (bi, block) in expected.blocks.iter_mut().enumerate() {
        let mut ni = 0usize;
        block.body.retain(|_| {
            let keep = !doomed.contains(&(bi, ni));
            ni += 1;
            keep
        });
    }
    Ok((
        expected,
        WitnessVerdict {
            exact: 0,
            refinements: doomed.len(),
        },
    ))
}

// ---------------------------------------------------------------------------
// Constant-table promotion
// ---------------------------------------------------------------------------

/// A displacement from the allocation's address in bytes: exact, an
/// unsigned `index` times `scale` plus `add`, or unknown.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Offset {
    Known(i128),
    Scaled {
        index: ValueId,
        scale: u128,
        add: i128,
    },
    Unknown,
}

impl Offset {
    fn plus(self, other: Offset) -> Offset {
        match (self, other) {
            (Offset::Known(a), Offset::Known(b)) => {
                a.checked_add(b).map_or(Offset::Unknown, Offset::Known)
            }
            (Offset::Known(a), Offset::Scaled { index, scale, add })
            | (Offset::Scaled { index, scale, add }, Offset::Known(a)) => a
                .checked_add(add)
                .map_or(Offset::Unknown, |add| Offset::Scaled { index, scale, add }),
            _ => Offset::Unknown,
        }
    }
}

/// A value computed from the promoted allocation's address.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Derived {
    /// A pointer of the allocation's provenance at this displacement.
    Pointer(Offset),
    /// A 32-bit integer equal to the address plus this displacement, modulo
    /// 2^32.
    Integer(Offset),
}

/// Whether `ty` is a wasm32 address-width integer.
fn address_int(ty: &Ty, pointer_bits: u32) -> bool {
    pointer_bits == 32 && matches!(ty, Ty::I32 | Ty::U32 | Ty::Isize | Ty::Usize)
}

/// The blocks reachable from the entry in reverse postorder of this module's
/// own walk, and each block's immediate dominator by position (the entry's
/// is itself, an unreachable block's `usize::MAX`), by the iterative
/// Cooper-Harvey-Kennedy intersection over `preds` (every incoming edge,
/// from [`incoming_edges`]). `None` when the entry is not a block.
fn dominator_tree(
    func: &Function,
    positions: &HashMap<BlockId, usize>,
    preds: &[Vec<usize>],
) -> Option<(Vec<usize>, Vec<usize>)> {
    let entry = *positions.get(&func.entry)?;
    let n = func.blocks.len();
    let mut order = Vec::with_capacity(n);
    let mut state = vec![0u8; n];
    let mut stack: Vec<(usize, usize)> = vec![(entry, 0)];
    state[entry] = 1;
    let succs: Vec<Vec<usize>> = func
        .blocks
        .iter()
        .map(|b| {
            b.body
                .last()
                .map(|t| t.inst.successor_edges())
                .unwrap_or_default()
                .iter()
                .filter_map(|e| positions.get(&e.target).copied())
                .collect()
        })
        .collect();
    while let Some((b, k)) = stack.pop() {
        if k < succs[b].len() {
            stack.push((b, k + 1));
            let s = succs[b][k];
            if state[s] == 0 {
                state[s] = 1;
                stack.push((s, 0));
            }
        } else {
            order.push(b);
        }
    }
    order.reverse();
    let mut rank = vec![usize::MAX; n];
    for (i, &b) in order.iter().enumerate() {
        rank[b] = i;
    }
    let mut idom = vec![usize::MAX; n];
    idom[entry] = entry;
    let mut changed = true;
    while changed {
        changed = false;
        for &b in order.iter().skip(1) {
            let mut new = usize::MAX;
            for &p in &preds[b] {
                if idom[p] == usize::MAX {
                    continue;
                }
                new = if new == usize::MAX {
                    p
                } else {
                    let (mut x, mut y) = (p, new);
                    while x != y {
                        while rank[x] > rank[y] {
                            x = idom[x];
                        }
                        while rank[y] > rank[x] {
                            y = idom[y];
                        }
                    }
                    x
                };
            }
            if new != usize::MAX && idom[b] != new {
                idom[b] = new;
                changed = true;
            }
        }
    }
    Some((order, idom))
}

/// The CTP checker's view of one function: definitions, dominators and the
/// unsigned bounds checks branches establish. Derived here from the source
/// alone (`trust_cg_irmid::escape` is the pass's analysis, not consulted).
struct BoundFacts<'f> {
    func: &'f Function,
    index: Defs<'f>,
    pointer_bits: u32,
    positions: HashMap<BlockId, usize>,
    preds: Vec<Vec<usize>>,
    /// Immediate dominators by position (`usize::MAX`: unreachable).
    idom: Vec<usize>,
    entry: usize,
}

impl<'f> BoundFacts<'f> {
    fn new(func: &'f Function, pointer_bits: u32) -> Option<Self> {
        let positions = block_positions(func);
        let preds = incoming_edges(func, &positions);
        let entry = *positions.get(&func.entry)?;
        let (_, idom) = dominator_tree(func, &positions, &preds)?;
        Some(Self {
            func,
            index: Defs::of(func),
            pointer_bits,
            positions,
            preds,
            idom,
            entry,
        })
    }

    /// `v` through copies, bitcasts between address-width integers, and an
    /// address-width truncation of a zero extension from at most that width
    /// (the rustc bridge's `trunc(zext(i))` index): each keeps the value's
    /// unsigned value.
    fn canon(&self, mut v: ValueId) -> ValueId {
        for _ in 0..64 {
            match self.index.inst(v) {
                Some(Inst::Copy { operand, .. }) => v = *operand,
                Some(Inst::Cast {
                    op: CastOp::Bitcast,
                    src_ty,
                    dst_ty,
                    operand,
                }) if address_int(src_ty, self.pointer_bits)
                    && address_int(dst_ty, self.pointer_bits) =>
                {
                    v = *operand;
                }
                Some(Inst::Cast {
                    op: CastOp::Trunc,
                    dst_ty,
                    operand,
                    ..
                }) if address_int(dst_ty, self.pointer_bits) => match self.index.inst(*operand) {
                    Some(Inst::Cast {
                        op: CastOp::ZExt,
                        src_ty,
                        operand: inner,
                        ..
                    }) if int_shape(src_ty, self.pointer_bits).is_some_and(|(w, _)| w <= 32) => {
                        v = *inner;
                    }
                    _ => break,
                },
                _ => break,
            }
        }
        v
    }

    /// The unsigned value of an integer constant `v` (through copies), read
    /// at its type's width.
    fn constant(&self, v: ValueId) -> Option<u128> {
        let Some(Inst::Const {
            ty,
            value: Constant::Int(c),
        }) = self.index.inst(self.canon(v))
        else {
            return None;
        };
        let (bits, _) = int_shape(ty, self.pointer_bits)?;
        let mask = if bits >= 128 {
            u128::MAX
        } else {
            (1u128 << bits) - 1
        };
        Some((*c as u128) & mask)
    }

    /// The amount `other` adds to a displacement.
    fn term(&self, other: ValueId) -> Offset {
        if let Some(c) = self.constant(other) {
            // An address-width constant read as a signed amount.
            let c = c as u32 as i32;
            return Offset::Known(i128::from(c));
        }
        let other = self.canon(other);
        match self.index.inst(other) {
            Some(Inst::BinOp {
                op: BinOp::Mul,
                lhs,
                rhs,
                ..
            }) => match (self.constant(*lhs), self.constant(*rhs)) {
                (_, Some(s)) => Offset::Scaled {
                    index: self.canon(*lhs),
                    scale: s,
                    add: 0,
                },
                (Some(s), _) => Offset::Scaled {
                    index: self.canon(*rhs),
                    scale: s,
                    add: 0,
                },
                _ => Offset::Scaled {
                    index: other,
                    scale: 1,
                    add: 0,
                },
            },
            Some(Inst::BinOp {
                op: BinOp::Shl,
                lhs,
                rhs,
                ..
            }) => match self.constant(*rhs) {
                Some(k) if k < 32 => Offset::Scaled {
                    index: self.canon(*lhs),
                    scale: 1u128 << k,
                    add: 0,
                },
                _ => Offset::Scaled {
                    index: other,
                    scale: 1,
                    add: 0,
                },
            },
            _ => Offset::Scaled {
                index: other,
                scale: 1,
                add: 0,
            },
        }
    }

    /// The largest unsigned value of the address-width integer `x` from its
    /// definition: a constant, a mask with or a remainder by one, or a zero
    /// extension from a narrower integer.
    fn defined_max(&self, x: ValueId) -> Option<u128> {
        if let Some(c) = self.constant(x) {
            return Some(c);
        }
        match self.index.inst(x)? {
            Inst::BinOp {
                op: BinOp::And,
                lhs,
                rhs,
                ..
            } => self.constant(*rhs).or_else(|| self.constant(*lhs)),
            Inst::BinOp {
                op: BinOp::URem,
                rhs,
                ..
            } => self.constant(*rhs).filter(|&m| m > 0).map(|m| m - 1),
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty,
                ..
            } => {
                let (bits, _) = int_shape(src_ty, self.pointer_bits)?;
                (bits < 32).then(|| (1u128 << bits) - 1)
            }
            _ => None,
        }
    }

    /// The bounds `x < limit` that hold in block `at`: the taken edge of an
    /// unsigned comparison of `x` with a constant into a block that has no
    /// other incoming edge and dominates `at`.
    fn guard_max(&self, x: ValueId, at: usize) -> Option<u128> {
        let mut best: Option<u128> = None;
        let mut block = at;
        loop {
            if block != self.entry
                && let [pred] = self.preds[block].as_slice()
                && let Some(Inst::CondBr {
                    cond,
                    then_target,
                    else_target,
                    ..
                }) = self.func.blocks[*pred].body.last().map(|n| &n.inst)
                && then_target != else_target
                && let Some(Inst::ICmp { op, lhs, rhs, .. }) = self.index.inst(self.canon(*cond))
            {
                let id = self.func.blocks[block].id;
                let taken_then = *then_target == id;
                let checked = match (op, taken_then) {
                    (ICmpOp::Ult, true) | (ICmpOp::Uge, false) => Some((*lhs, *rhs)),
                    (ICmpOp::Ugt, true) | (ICmpOp::Ule, false) => Some((*rhs, *lhs)),
                    _ => None,
                };
                if let Some((index, limit)) = checked
                    && self.canon(index) == x
                    && let Some(limit) = self.constant(limit)
                    && limit > 0
                {
                    best = Some(best.map_or(limit - 1, |b| b.min(limit - 1)));
                }
            }
            if block == self.entry {
                break;
            }
            let up = self.idom[block];
            if up == usize::MAX || up == block {
                break;
            }
            block = up;
        }
        best
    }

    /// Whether an address at `offset` from an allocation of `size` bytes, in
    /// block `at`, provably lies inside it (`[0, size)`), so that `inttoptr`
    /// of it resolves to the allocation. The integer arithmetic is modulo
    /// 2^32; the exact displacement is below `size`, and an allocation's last
    /// byte is addressable, so no step wraps the sum.
    fn inside(&self, offset: Offset, size: u64, at: usize) -> bool {
        let size = i128::from(size);
        match offset {
            Offset::Known(c) => (0..size).contains(&c),
            Offset::Scaled { index, scale, add } if add >= 0 => {
                let maxes = [self.defined_max(index), self.guard_max(index, at)];
                maxes.into_iter().flatten().any(|m| {
                    i128::try_from(m)
                        .ok()
                        .and_then(|m| m.checked_mul(i128::try_from(scale).ok()?))
                        .and_then(|top| top.checked_add(add))
                        .is_some_and(|top| top < size)
                })
            }
            _ => false,
        }
    }
}

/// The little-endian bytes a plain store of the constant `value` of type `ty`
/// writes (integers in two's complement at their width, `bool` as 0 or 1),
/// or `None` for any other type or a constant outside its type's range.
fn constant_bytes(ty: &Ty, value: &Constant, pointer_bits: u32) -> Option<Vec<u8>> {
    let (raw, bytes) = match (ty, value) {
        (Ty::Bool, Constant::Bool(b)) => (u128::from(*b), 1),
        (_, Constant::Int(c)) => {
            let (bits, signed) = int_shape(ty, pointer_bits)?;
            if !fits(*c, bits, signed) {
                return None;
            }
            (*c as u128, bits / 8)
        }
        (Ty::U128, Constant::U128(u)) => (*u, 16),
        _ => return None,
    };
    Some(raw.to_le_bytes()[..bytes as usize].to_vec())
}

/// What the promotion of one allocation found.
struct Promotable {
    stores: BTreeSet<(usize, usize)>,
    image: Vec<Option<u8>>,
}

/// Re-derive, on the source, that `alloca` (at `at`) may become a read-only
/// global: every value computed from its address is a pointer of its
/// provenance or a 32-bit integer equal to the address plus a displacement,
/// moved only by copies, `gep`, `ptrtoint`/`inttoptr` (the latter only where
/// the displacement provably lies in the allocation), bitcasts and additions
/// of independent amounts; it is never compared, branched on, returned,
/// passed, stored or given to a block; and every write through it is a plain
/// store of an integer or `bool` constant at a known displacement inside it.
fn promotable(
    facts: &BoundFacts<'_>,
    uses: &HashMap<ValueId, Vec<(usize, usize)>>,
    alloca: ValueId,
    size: u64,
) -> Result<Promotable, String> {
    let pointer_bits = facts.pointer_bits;
    let mut known: HashMap<ValueId, Derived> =
        HashMap::from([(alloca, Derived::Pointer(Offset::Known(0)))]);
    let mut pending = vec![alloca];
    let mut out = Promotable {
        stores: BTreeSet::new(),
        image: vec![None; size as usize],
    };
    let mut loads = 0usize;
    while let Some(d) = pending.pop() {
        let fact = known[&d];
        for &(bi, ni) in uses.get(&d).map_or(&[][..], Vec::as_slice) {
            let node = &facts.func.blocks[bi].body[ni];
            let refuse = |why: &str| {
                Err(format!(
                    "{why} (block {}, instruction {ni})",
                    facts.func.blocks[bi].id
                ))
            };
            let derived = |v: &ValueId| known.contains_key(v);
            let result = match (&node.inst, fact) {
                (Inst::Copy { operand, .. }, _) if *operand == d => Some(fact),
                (
                    Inst::GEP {
                        pointee_ty,
                        base,
                        indices,
                        ..
                    },
                    Derived::Pointer(offset),
                ) if *base == d && !indices.iter().any(derived) => {
                    // A byte `gep` by one address-width constant moves the
                    // pointer by that many bytes; any other keeps the
                    // provenance at an unknown displacement.
                    let step = match (pointee_ty, indices.as_slice()) {
                        (Ty::U8 | Ty::I8, [k]) => match facts.index.inst(*k) {
                            Some(Inst::Const {
                                ty,
                                value: Constant::Int(k),
                            }) if address_int(ty, pointer_bits) => Offset::Known(*k),
                            _ => Offset::Unknown,
                        },
                        _ => Offset::Unknown,
                    };
                    Some(Derived::Pointer(offset.plus(step)))
                }
                (
                    Inst::Cast {
                        op: CastOp::PtrToInt,
                        src_ty: Ty::Ptr,
                        dst_ty,
                        ..
                    },
                    Derived::Pointer(offset),
                ) if address_int(dst_ty, pointer_bits) => Some(Derived::Integer(offset)),
                (
                    Inst::Cast {
                        op: CastOp::Bitcast,
                        src_ty,
                        dst_ty,
                        ..
                    },
                    Derived::Integer(_),
                ) if address_int(src_ty, pointer_bits) && address_int(dst_ty, pointer_bits) => {
                    Some(fact)
                }
                (
                    Inst::Cast {
                        op: CastOp::IntToPtr,
                        src_ty,
                        dst_ty: Ty::Ptr,
                        ..
                    },
                    Derived::Integer(offset),
                ) if address_int(src_ty, pointer_bits) => {
                    if !facts.inside(offset, size, bi) {
                        return refuse("an integer address may leave the allocation");
                    }
                    Some(Derived::Pointer(offset))
                }
                (
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty,
                        lhs,
                        rhs,
                    },
                    Derived::Integer(offset),
                ) if address_int(ty, pointer_bits) && (*lhs == d) != (*rhs == d) => {
                    let other = if *lhs == d { *rhs } else { *lhs };
                    if derived(&other) {
                        return refuse("two addresses are added");
                    }
                    Some(Derived::Integer(offset.plus(facts.term(other))))
                }
                (
                    Inst::BinOp {
                        op: BinOp::Sub,
                        ty,
                        lhs,
                        rhs,
                    },
                    Derived::Integer(offset),
                ) if address_int(ty, pointer_bits) && *lhs == d && *rhs != d => {
                    let Some(c) = facts.constant(*rhs) else {
                        return refuse("a non-constant amount is subtracted from the address");
                    };
                    let c = i128::from(c as u32 as i32);
                    Some(Derived::Integer(
                        c.checked_neg()
                            .map_or(Offset::Unknown, |n| offset.plus(Offset::Known(n))),
                    ))
                }
                (
                    Inst::Load {
                        ptr,
                        volatile: false,
                        ..
                    },
                    Derived::Pointer(_),
                ) if *ptr == d => {
                    loads += 1;
                    None
                }
                (
                    Inst::Store {
                        ty,
                        ptr,
                        value,
                        volatile: false,
                        ..
                    },
                    Derived::Pointer(offset),
                ) if *ptr == d && !derived(value) => {
                    let Offset::Known(at) = offset else {
                        return refuse("a store at an unknown displacement");
                    };
                    let Some(Inst::Const { ty: c_ty, value: c }) = facts.index.inst(*value) else {
                        return refuse("a store of a non-constant value");
                    };
                    if c_ty != ty {
                        return refuse("a store of a constant of another type");
                    }
                    let Some(bytes) = constant_bytes(ty, c, pointer_bits) else {
                        return refuse("a store of a constant this checker does not encode");
                    };
                    let start = u64::try_from(at)
                        .map_err(|_| "a store before the allocation".to_string())?;
                    let end = start + bytes.len() as u64;
                    if end > size {
                        return refuse("a store past the allocation");
                    }
                    for (k, byte) in bytes.iter().enumerate() {
                        let slot = &mut out.image[start as usize + k];
                        if slot.is_some_and(|b| b != *byte) {
                            return refuse("two stores write different bytes");
                        }
                        *slot = Some(*byte);
                    }
                    out.stores.insert((bi, ni));
                    None
                }
                _ => return refuse("the address is used other than as a promotable table"),
            };
            if let Some(f) = result {
                let [r] = node.results.as_slice() else {
                    return refuse("a derived instruction has no single result");
                };
                if let Some(old) = known.insert(*r, f) {
                    if old != f {
                        return refuse("a value is derived twice");
                    }
                } else {
                    pending.push(*r);
                }
            }
        }
    }
    if loads == 0 {
        return Err("the table is never read".to_string());
    }
    Ok(out)
}

fn rebuild_ctp(
    module: &Module,
    pointer_bits: u32,
    source: &Function,
    witness: &CtpWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let bad_global = |why: String| MidTvError::BadGlobal { why };
    if witness.new_globals.len() != witness.promotions.len() {
        return Err(bad_global(
            "one new global per promotion is required".to_string(),
        ));
    }
    let base_type = module.types.len();
    for (i, ty) in witness.new_types.iter().enumerate() {
        if *ty != Ty::U8 {
            return Err(bad_global(format!("new type {} is not u8", base_type + i)));
        }
    }
    let resolve_ty = |id: trust_ir::TyId| -> Option<&Ty> {
        module
            .ty(id)
            .or_else(|| witness.new_types.get(id.as_usize().checked_sub(base_type)?))
    };
    let facts = BoundFacts::new(source, pointer_bits).ok_or(MidTvError::TargetDiffers {
        detail: "the source has no entry block".to_string(),
    })?;
    let defs = definitions(source);
    let uses = use_positions(source);
    let layout = FsymLayout::new(module);
    let mut names: HashSet<&str> = module
        .globals
        .iter()
        .map(|g| g.name.as_str())
        .chain(module.functions.iter().map(|f| f.name.as_str()))
        .collect();
    let mut doomed: HashSet<(usize, usize)> = HashSet::new();
    let mut replaced: HashMap<(usize, usize), GlobalId> = HashMap::new();
    let mut verdict = WitnessVerdict::default();
    for (j, (promotion, global)) in witness
        .promotions
        .iter()
        .zip(&witness.new_globals)
        .enumerate()
    {
        let alloca = promotion.alloca;
        let bad = |why: String| MidTvError::NotPromotable { alloca, why };
        let id = u32::try_from(module.globals.len() + j)
            .map(GlobalId::new)
            .map_err(|_| bad("the global table is full".to_string()))?;
        if promotion.global != id {
            return Err(bad(format!(
                "the promotion names global {} where the next new global is {}",
                promotion.global, id
            )));
        }
        let at = match defs.get(&alloca) {
            Some(Some(at)) => *at,
            _ => return Err(bad("not defined by an instruction".to_string())),
        };
        let node = &source.blocks[at.0].body[at.1];
        if source.blocks[at.0].id != promotion.block || at.1 != promotion.index {
            return Err(bad(
                "the allocation is not at the claimed position".to_string()
            ));
        }
        let Inst::Alloca {
            ty,
            count: None,
            align,
        } = &node.inst
        else {
            return Err(bad("not a count-free alloca".to_string()));
        };
        if node.results != [alloca] || replaced.contains_key(&at) {
            return Err(bad("not a count-free alloca, or promoted twice".to_string()));
        }
        let size = layout
            .size(ty)
            .map_err(|e| bad(format!("the allocation has no layout: {e}")))?;
        let natural = layout
            .align(ty)
            .map_err(|e| bad(format!("the allocation has no layout: {e}")))?;
        let want_align = align.unwrap_or(natural);
        if size == 0 {
            return Err(bad("the allocation is empty".to_string()));
        }
        let found = promotable(&facts, &uses, alloca, size).map_err(bad)?;
        let mut claimed = BTreeSet::new();
        for (block, index) in &promotion.stores {
            let bi = *facts
                .positions
                .get(block)
                .ok_or(bad("a claimed store is not in the function".to_string()))?;
            claimed.insert((bi, *index));
        }
        if claimed != found.stores || claimed.len() != promotion.stores.len() {
            return Err(bad(
                "the claimed stores are not the table's stores".to_string()
            ));
        }
        let data: Vec<u8> = found.image.iter().map(|b| b.unwrap_or(0)).collect();
        if data.len() >= 2 && data.iter().all(|b| *b == data[0]) {
            return Err(bad(
                "a uniform image is spelled as a splat, not as bytes".to_string()
            ));
        }
        // The global: a fresh, read-only, internal `[u8 x size]` with exactly
        // the image's bytes (undefined bytes as 0) and the allocation's
        // alignment.
        let Ty::Array(elem, len) = &global.ty else {
            return Err(bad_global(format!("`{}` is not a byte array", global.name)));
        };
        if *len != size || resolve_ty(*elem) != Some(&Ty::U8) {
            return Err(bad_global(format!(
                "`{}` is not a [u8 x {size}]",
                global.name
            )));
        }
        let expected_global = Global {
            name: global.name.clone(),
            ty: global.ty.clone(),
            mutable: false,
            initializer: Some(Constant::Bytes { data, utf8: false }),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: u32::try_from(want_align).ok(),
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        };
        if *global != expected_global {
            return Err(bad_global(format!(
                "`{}` is not the read-only image of the table",
                global.name
            )));
        }
        if !names.insert(global.name.as_str()) {
            return Err(bad_global(format!("`{}` is not a fresh name", global.name)));
        }
        // A refinement: on a path that reads a byte before its store, or a
        // byte no store writes, the source reads poison (or faults) where the
        // target reads the image's byte.
        verdict.refinements += 1;
        replaced.insert(at, id);
        doomed.extend(found.stores);
    }
    let mut expected = source.clone();
    for (&(bi, ni), &global) in &replaced {
        expected.blocks[bi].body[ni].inst = Inst::GlobalAddr { global };
    }
    for (bi, block) in expected.blocks.iter_mut().enumerate() {
        let mut ni = 0usize;
        block.body.retain(|_| {
            let keep = !doomed.contains(&(bi, ni));
            ni += 1;
            keep
        });
    }
    Ok((expected, verdict))
}

// ---------------------------------------------------------------------------
// Interpreter differential
// ---------------------------------------------------------------------------

/// Bounds of one differential run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DifferentialBudget {
    /// Interpreter steps one run may take: the whole budget of a
    /// [`run_samples`] run, and the least a [`Harness`] run's cap is.
    pub fuel_per_run: u64,
    /// The most a [`Harness`] run's cap is.
    pub max_fuel_per_run: u64,
    /// The most a [`Harness`] run's cap is when a loop it can reach
    /// allocates (each step's cost grows with the allocations a run keeps).
    pub max_fuel_per_allocating_loop: u64,
    /// A [`Harness`] run's cap per instruction of the function and of the
    /// module functions it reaches through direct calls, times one more than
    /// the loops (retreating edges) among them.
    pub fuel_per_instruction: u64,
    /// Call depth one run may reach.
    pub max_call_depth: u64,
}

impl Default for DifferentialBudget {
    fn default() -> Self {
        Self {
            fuel_per_run: 20_000,
            max_fuel_per_run: 262_144,
            max_fuel_per_allocating_loop: 65_536,
            fuel_per_instruction: 2_048,
            max_call_depth: 32,
        }
    }
}

/// How one interpreter run ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SampleOutcome {
    /// The function returned these values.
    Returned(Vec<InterpretValue>),
    /// A check failed: the structured panic and its message.
    Panicked(Option<Box<InterpretPanic>>, String),
    /// Undefined behaviour, or an `assume` the input violates: the input is
    /// excluded from the comparison (the refinement rule).
    Undefined,
    /// The interpreter could not finish the run (its error code); never
    /// counted as agreement.
    NotExecuted(&'static str),
}

/// Run `func` (resolved against `module` for its callees) on every input.
/// Returns the outcomes and an upper bound on the steps spent.
pub fn run_samples(
    module: &Module,
    func: &Function,
    inputs: &[Vec<InterpretValue>],
    budget: DifferentialBudget,
) -> (Vec<SampleOutcome>, u64) {
    let options = InterpretOptions {
        fuel: budget.fuel_per_run,
        max_call_depth: budget.max_call_depth,
        ..InterpretOptions::default()
    };
    let interpreter = Interpreter::with_module(module).with_options(options);
    let mut steps = 0u64;
    let mut outcomes = Vec::with_capacity(inputs.len());
    for args in inputs {
        let run = catch_unwind(AssertUnwindSafe(|| {
            interpreter.execute_function(func, args.iter().cloned())
        }));
        let outcome = match run {
            Ok(Ok(done)) => {
                steps = steps.saturating_add(done.steps);
                if done.host_calls == 0 {
                    SampleOutcome::Returned(done.returns)
                } else {
                    SampleOutcome::NotExecuted("host_assisted")
                }
            }
            Ok(Err(error)) => {
                steps = steps.saturating_add(budget.fuel_per_run);
                match error.code {
                    InterpretErrorCode::UndefinedBehavior | InterpretErrorCode::AssumeViolated => {
                        SampleOutcome::Undefined
                    }
                    InterpretErrorCode::Panic => {
                        SampleOutcome::Panicked(error.panic, error.message)
                    }
                    code => SampleOutcome::NotExecuted(code.as_str()),
                }
            }
            Err(_) => {
                steps = steps.saturating_add(budget.fuel_per_run);
                SampleOutcome::NotExecuted("interpreter_fault")
            }
        };
        outcomes.push(outcome);
    }
    (outcomes, steps)
}

/// The comparison of a source and a target run over the same inputs.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DifferentialReport {
    /// Inputs on which both runs were compared and agreed.
    pub compared: usize,
    /// Inputs excluded because the source raised undefined behaviour.
    pub ub_excluded: usize,
    /// Inputs the interpreter could not finish on the source.
    pub not_executed: usize,
    /// The first disagreement, if any.
    pub mismatch: Option<String>,
}

/// Compare outcomes input by input under the refinement rule.
pub fn compare_samples(source: &[SampleOutcome], target: &[SampleOutcome]) -> DifferentialReport {
    let mut report = DifferentialReport::default();
    if source.len() != target.len() {
        report.mismatch = Some("the runs cover different inputs".to_string());
        return report;
    }
    for (index, (s, t)) in source.iter().zip(target).enumerate() {
        match s {
            SampleOutcome::Undefined => report.ub_excluded += 1,
            SampleOutcome::NotExecuted(_) => report.not_executed += 1,
            SampleOutcome::Returned(_) | SampleOutcome::Panicked(..) => {
                if s == t {
                    report.compared += 1;
                } else if report.mismatch.is_none() {
                    report.mismatch = Some(format!(
                        "input {index}: source {}, target {}",
                        describe(s),
                        describe(t)
                    ));
                }
            }
        }
    }
    report
}

fn describe(outcome: &SampleOutcome) -> String {
    match outcome {
        SampleOutcome::Returned(values) => format!("returned {} value(s)", values.len()),
        SampleOutcome::Panicked(_, message) => format!("panicked ({message})"),
        SampleOutcome::Undefined => "raised undefined behaviour".to_string(),
        SampleOutcome::NotExecuted(code) => format!("did not finish ({code})"),
    }
}

/// `count` deterministic argument vectors for `func`, or `None` when a
/// parameter has a type this module does not synthesize (pointers,
/// aggregates, handles). Integers draw from boundary values and a seeded
/// generator; booleans from both values; floats from a fixed set.
pub fn seeded_inputs(
    module: &Module,
    func: &Function,
    pointer_bits: u32,
    count: usize,
    seed: u64,
) -> Option<Vec<Vec<InterpretValue>>> {
    let params = &module.func_type(func.ty)?.params;
    let mut state = seed ^ 0x9e37_79b9_7f4a_7c15;
    let mut inputs = Vec::with_capacity(count);
    for sample in 0..count {
        let mut args = Vec::with_capacity(params.len());
        for ty in params {
            args.push(sample_value(ty, pointer_bits, sample, &mut state)?);
        }
        inputs.push(args);
    }
    Some(inputs)
}

fn splitmix(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn sample_value(
    ty: &Ty,
    pointer_bits: u32,
    sample: usize,
    state: &mut u64,
) -> Option<InterpretValue> {
    let draw = splitmix(state);
    match ty {
        Ty::Bool => Some(InterpretValue::bool(draw & 1 == 1)),
        Ty::F32 | Ty::F64 => {
            const VALUES: [f64; 6] = [0.0, 1.0, -1.5, 3.25, -0.0, 1.0e10];
            let value = VALUES[(draw % VALUES.len() as u64) as usize];
            let bits = if matches!(ty, Ty::F32) {
                u64::from((value as f32).to_bits())
            } else {
                value.to_bits()
            };
            Some(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::FloatBits(bits),
            })
        }
        _ => {
            let (bits, signed) = int_shape(ty, pointer_bits)?;
            let raw: i128 = match (sample + (draw as usize)) % 6 {
                0 => 0,
                1 => 1,
                2 => (draw % 64) as i128,
                3 => {
                    if signed {
                        -1
                    } else {
                        2
                    }
                }
                4 => {
                    // The type's maximum.
                    if bits >= 128 {
                        if signed { i128::MAX } else { -1 }
                    } else if signed {
                        (1i128 << (bits - 1)) - 1
                    } else {
                        (1i128 << bits) - 1
                    }
                }
                _ => (i128::from(draw) << 64) | i128::from(splitmix(state)),
            };
            // Truncate to the type's width, two's complement, then read it
            // back in the type's signedness.
            let value = if bits >= 128 {
                if signed {
                    raw
                } else {
                    // `from_raw` would be the unsigned reading; keep the
                    // non-negative half so `int_at` accepts it.
                    raw & i128::MAX
                }
            } else {
                let mask = (1i128 << bits) - 1;
                let low = raw & mask;
                if signed && low >= (1i128 << (bits - 1)) {
                    low - (1i128 << bits)
                } else {
                    low
                }
            };
            InterpretValue::int_at(ty.clone(), value, pointer_bits).ok()
        }
    }
}

#[path = "trust_ir_mid_tv_harness.rs"]
mod harness;

pub use harness::{
    FUEL_LADDER_FACTOR, FUEL_LADDER_START, Harness, HarnessLimits, InputOutcome, InputRun,
    InputVerdict, NotSynthesized, Observed, ReadPlan, Reading, compare_input, global_addr_stub,
    interpretable, interpretable_module, not_executed, run_inputs, run_target,
};

#[cfg(test)]
#[path = "trust_ir_mid_tv_tests.rs"]
mod tests;
