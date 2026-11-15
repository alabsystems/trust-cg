// trust-cg-verify/trust_ir_mid_tv_harness.rs - inputs and drivers for the mid-end differential
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The differential leg's inputs and runs ([`Harness`]), for every function
//! whose parameters this module can build a value of, and the module the runs
//! interpret ([`interpretable_module`]).
//!
//! **Scalar parameters** are drawn by [`super::seeded_inputs`] (the inputs the
//! scalar-only differential drew). A function with scalar parameters only
//! runs directly when it reaches no global, and under a driver (below) that
//! takes the globals' addresses first when it does.
//!
//! **Pointer, slice and by-value aggregate parameters** need memory, and every
//! run of trust-ir's reference interpreter starts with empty memory. So the
//! function runs under a DRIVER: a one-block function this module builds per
//! input, whose parameters are the scalar arguments, that allocates the
//! input's objects, writes their bytes, stores the address of each child
//! object into its parent's pointer slot, takes the address of the globals
//! (below), builds each argument (a pointer cast to the parameter's type, a
//! fat pointer from an object and a length, or a typed load of an aggregate
//! from its object), allocates a one-byte MARKER, calls the function, and
//! returns its results, the bytes it reads back from the objects after the
//! call and the marker. The interpreter executes the call and, through it,
//! the bodies of the module functions it reaches (a declaration is not
//! executable and ends the run as not executed).
//!
//! **Globals.** A driver takes the address of the globals the function names
//! and of those the module functions it reaches through direct calls name
//! (at most [`HarnessLimits::max_reached_globals`] beyond its own), so each
//! is allocated, and its initializer materialized, before the call, in the
//! same order for the source and the target, and a pointer to one keeps its
//! identity in the comparison. When materializing them all fails, the
//! function's own are taken, else none (a global first reached during the
//! call is then allocated after the marker, like any allocation made there).
//! A global only the target names (one a rewrite adds) is allocated during
//! the call.
//!
//! **Aliasing inputs.** Every input gives each memory parameter its own
//! objects, except two more inputs drawn for a function with two or more
//! pointer or slice parameters: one binds all of them to the start of one
//! shared object, and one binds the second `step` bytes into the first's
//! object (half the first's constant extent, between 1 and 4 bytes, or 4
//! when it is accessed at a variable offset), so their accesses overlap
//! partly. The shared object is planned from the union of the parameters'
//! needs at those offsets; an aliasing input whose object is past the
//! limits is not drawn. Other pairings of three or more parameters, and
//! other offsets, are not exercised.
//!
//! **What an input's memory is.** The objects are planned from the function's
//! own accesses ([`Need`]): each pointer parameter (and every pointer value
//! derived from it by `copy`, pointer casts, `gep`, `ptrtoint`/`add`/`sub`
//! of a constant/`inttoptr`, block arguments and `select`) is followed to its
//! loads, stores and bulk operations, which give the object's extent at
//! constant offsets (an access at a variable offset makes it OPEN, and the
//! object gets [`HarnessLimits::open_slack`] more bytes), and to the calls it
//! is passed to, whose parameter is analysed the same way (to
//! [`HarnessLimits::max_call_depth`] levels). A pointer LOADED from a
//! constant offset (or an address-width integer loaded there and turned into
//! a pointer) makes that offset a POINTER SLOT, whose child object is planned
//! from the loaded value's own uses (to [`HarnessLimits::max_slot_depth`]
//! levels). A parameter typed `&T`, `&mut T`, `*const T` or `*mut T` also
//! sizes its object by `T` and fills it by `T`'s layout (`fsym_layout`, the
//! interpreter's): integers, `bool` (0 or 1), `char`, floats and pointer
//! fields (which become slots). Bytes no typed field covers are filled with
//! small words. The fill varies by input (zeros, ones, small seeded values,
//! seeded bytes); slice lengths vary from 0 to 8.
//!
//! **What a run observes.** A run's outcome is the function's results and
//! the bytes it reads back from the input's objects after the call, compared
//! under the refinement rule: an input on which the SOURCE raises undefined
//! behaviour is excluded. The source reads every byte of every object first.
//! When that read meets a byte the function left uninitialised (struct
//! padding an aggregate store wrote, poison, an unwritten lane), the input is
//! run once without reading back; if the call itself returned, the read is
//! narrowed: the reported byte and the rest of its 4-byte word are left
//! unread, in the first object in reading order that reads it, and the input
//! is run again, at most [`HarnessLimits::max_read_probes`] times; then only
//! what the last failure proves initialised is read (every object read
//! before it, and the failing object's bytes below it), or nothing. A
//! candidate runs each input with its source's reading ([`Reading`]): it
//! must give the same results and the same bytes wherever the source's are
//! read, and a byte the candidate leaves uninitialised there is undefined
//! behaviour where the source had none, a disagreement. Bytes the source
//! left uninitialised are not compared (the candidate may define them).
//! Pointer values are compared up to a renaming of the allocations made
//! during the call (by order of first appearance; allocations made before
//! the marker keep their identity); pointer BYTES in an object are
//! addresses and are compared as bytes, so an allocation made during the
//! call whose address the function stores into an object is compared by its
//! address. What a compared input observed is named ([`Observed`]): memory,
//! results (or the structured panic), or only that both returned, which
//! observes nothing a rewrite could change except termination and is not
//! counted as a comparison.
//!
//! **What an input is not.** For a function with memory parameters the
//! driver's own prefix (allocation, writes, globals and argument
//! construction) is run alone first; an input on which it raises
//! undefined behaviour (bytes that are not a value of a by-value parameter's
//! type, such as an enum tag no variant has) is INVALID and never run.
//!
//! **Fuel.** A run gets [`DifferentialBudget::fuel_per_instruction`] steps per
//! instruction of the function and of the module functions it can reach
//! through direct calls, clamped to `[fuel_per_run, max_fuel_per_run]`, and
//! climbs to that cap through a ladder ([`FUEL_LADDER_START`], times
//! [`FUEL_LADDER_FACTOR`]): a run is retried with the next rung only when it
//! ran out of fuel, so the steps charged to a run that does not finish are at
//! most [`FUEL_LADDER_FACTOR`] times the steps it took (all of them for the
//! first rung), and a run that finishes is charged what it took plus the
//! rungs below.
//!
//! **The interpreter's view of the lane's idioms.** The rustc bridge's
//! modules use forms the wasm lane compiles with a defined meaning and the
//! reference interpreter refuses as type errors. The runs interpret a VIEW of
//! the module ([`interpretable`], [`interpretable_module`]) that spells each in
//! the interpreter's typed form, with the meaning the lane gives it:
//!
//! * a `copy`, binary operand, comparison operand, `select` arm, stored value,
//!   returned value, block argument or call argument of another integer type
//!   of the same width, or of another pointer-like type, is cast to the
//!   declared type first (`bitcast` / `ptrtoptr`: the lane moves the bits);
//!   a shift or rotate amount of a narrower integer type is zero-extended;
//! * a pointer comparison compares the two addresses (`ptrtoint` to
//!   `usize`);
//! * a `bool` constant spelled `0` or `1` is `false` or `true`; a pointer
//!   constant spelled as an integer is `inttoptr` of it, except the bridge's
//!   global-address stub (`0xFADE << 48 | index << 32 | offset`,
//!   [`global_addr_stub`]), which is that global's address plus the offset,
//!   as is a `symaddr` constant naming a global;
//! * a bulk-memory byte count of a signed type is read unsigned;
//! * a plain load or store has alignment 1: wasm loads and stores never fault
//!   on alignment (the lane's alignment is a hint);
//! * the bridge's write-through `insertfield` and read-through `extractfield`
//!   over a pointer (the lane stores or loads lane `field` of the declared
//!   aggregate through it), `extractfield` in the declared-aggregate spelling
//!   and over an array (the interpreter's lane and element forms), and the
//!   reinterpreting `extractfield` over an aggregate of another type of the
//!   same size (the lane reads lane `field` of the declared type over its
//!   bytes);
//! * an aggregate passed or returned by value where the value is a pointer
//!   is the pointee's bytes (the lane passes such an aggregate by address);
//! * an entry parameter declared with another pointer-like type than the
//!   signature's takes the signature's;
//! * a global whose pointer word is initialized with another global's
//!   address (`symaddr` at `ptr`, a relocation) is retyped `*const u8`, where
//!   the interpreter resolves it;
//! * a global without an initializer (a declaration: the bridge declares a
//!   static another unit defines at a placeholder type, `ptr`, whatever its
//!   real size) is retyped to an array of [`EXTERN_GLOBAL_RESERVE`] bytes
//!   (of a one-byte integer, or another small type, already in the type
//!   table: the view adds no type) when its declared type is smaller,
//!   keeping its natural alignment: its real extent is
//!   unknown here, and an access past the declared size through an address
//!   computed as an integer would otherwise resolve to the interpreter
//!   allocation placed after it. The interpreter zero-fills a global without
//!   an initializer (`.bss`), so the whole reserve reads as zero until the
//!   run writes it, for the source and the target alike: the static's real
//!   contents are unknown and both runs see the same stand-in, never another
//!   allocation's bytes. An access more than [`EXTERN_GLOBAL_RESERVE`] bytes
//!   past the global's address is not covered;
//! * a DECLARATION (no body) named `memmove`, `memcpy` or `memset` with the
//!   C prototype (three parameters, not variadic, one pointer-like result;
//!   a pointer-like destination, a pointer-like source or an integer fill
//!   of 9 to 32 bits, so that its truncation to `u8` narrows, an unsigned
//!   count of pointer width) has the body
//!   of the C library's operation: the count is read as `usize`, the fill
//!   truncated to `u8`, then `memcopy overlap` (`memmove`), `memcopy`
//!   (`memcpy`) or `memset`, and the destination is returned. The lane
//!   links the C library's functions for these calls (`compiler_builtins`
//!   on wasm32), and rustc's and LLVM's lowering of `ptr::copy`,
//!   `copy_nonoverlapping` and `write_bytes` relies on that meaning; a
//!   function the module defines under one of these names keeps its body.
//!
//! The C-library declaration premise above remains conditional (OD-143);
//! it is not strengthened here. A declaration named `memcmp` or `bcmp`
//! keeps its declaration in this view: the default wasm32 profile withholds
//! the comparison-call rewrite, and the differential gets no body for it
//! (OD-164's merge boundary). Only the comparison-call checker's tests run
//! in a view that gives such a declaration with the C prototype (three
//! parameters, not variadic; two pointer-like ones, an integer count of
//! pointer width, a 32-bit integer result) the C library's comparison: the
//! count's bits read as `usize`, every one of the `n` byte pairs loaded and
//! compared as unsigned chars (so an uninitialised byte among them is
//! undefined behaviour, as C requires both objects to hold `n` bytes), and
//! the difference of the first pair that differs returned
//! (`compiler_builtins`' value), or 0. A declaration named
//! `__trustcg_array_fill_iW` keeps its declaration: a name and signature do
//! not supply the bridge's helper body or authenticate a host implementation
//! (OD-155).
//!
//! The view is applied to the source and the target alike, never to the
//! module the mid-end emits; a form outside this list keeps the
//! interpreter's reading, and a run it stops is counted as not executed.
//!
//! Every count is of what ran: an input is compared only when the source and
//! the target both ran to completion on it (returned, or panicked with the
//! structured panic) and it observed results, a panic or memory; nothing
//! here is a proof.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::panic::{AssertUnwindSafe, catch_unwind};

use trust_ir::interpret::{
    ArrayValue, InterpretError, InterpretErrorCode, InterpretOptions, InterpretOutcome,
    InterpretPanic, InterpretPointer, InterpretValue, InterpretValueKind, Interpreter,
};
use trust_ir::node::InstrNode;
use trust_ir::value::{FuncTyId, GlobalId, TyId};
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, FatPtrKind, FuncId, FuncTy, Function, Inst, Module,
    Ty, ValueId,
};

use super::{DifferentialBudget, int_shape, seeded_inputs, splitmix};
use crate::fsym_layout::FsymLayout;

/// The first rung of the fuel ladder.
pub const FUEL_LADDER_START: u64 = 4_096;
/// How much each rung of the fuel ladder multiplies the previous one's fuel.
pub const FUEL_LADDER_FACTOR: u64 = 8;
/// The most instructions counted when sizing a run's fuel.
const STATIC_SIZE_CAP: u64 = 1 << 20;
/// Slice lengths drawn per input, in order.
const SLICE_LENS: [u64; 8] = [0, 1, 2, 3, 4, 8, 1, 5];
/// The largest slice length drawn.
const SLICE_LEN_MAX: u64 = 8;
/// The alignment of every object a driver allocates (over-alignment admits
/// every access the function's own alignment does).
const OBJECT_ALIGN: u64 = 16;

/// Bounds of input synthesis for one function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HarnessLimits {
    /// The most objects one input allocates.
    pub max_objects: usize,
    /// The most bytes all of one input's objects hold together.
    pub max_bytes: u64,
    /// Bytes added to an object some access reaches at a variable offset.
    pub open_slack: u64,
    /// How many pointer slots deep objects are planned.
    pub max_slot_depth: u32,
    /// How many calls deep a parameter's accesses are followed.
    pub max_call_depth: u32,
    /// Instructions the access analysis may visit for one function.
    pub max_visits: usize,
    /// Extra runs one input may spend narrowing the bytes it reads back
    /// when the function left some of them uninitialised.
    pub max_read_probes: u32,
    /// The most globals, beyond the function's own, a driver takes the
    /// address of before the call.
    pub max_reached_globals: usize,
}

impl Default for HarnessLimits {
    fn default() -> Self {
        Self {
            max_objects: 32,
            max_bytes: 64 * 1024,
            open_slack: 256,
            max_slot_depth: 3,
            max_call_depth: 4,
            max_visits: 200_000,
            max_read_probes: 8,
            max_reached_globals: 64,
        }
    }
}

/// Why no input of a function can be built: a stable key and the detail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NotSynthesized {
    /// `function_pointer`, `trait_object`, `closure`, `handle`,
    /// `collection`, `no_layout`, `unsupported_type`, `too_large` or
    /// `no_signature`.
    pub reason: &'static str,
    pub detail: String,
}

// ---------------------------------------------------------------------------
// What a pointer parameter must reach: the access analysis
// ---------------------------------------------------------------------------

/// The memory one pointer value is used to reach, relative to the address it
/// holds.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Need {
    /// Bytes accessed at constant offsets: the largest `offset + size`.
    extent: u64,
    /// Some access is at an offset this analysis does not know.
    open: bool,
    /// Pointer words loaded at constant offsets, and what each must reach.
    slots: BTreeMap<u64, Need>,
}

impl Need {
    fn access(&mut self, at: Option<u64>, size: u64) {
        match at {
            Some(offset) => self.extent = self.extent.max(offset.saturating_add(size)),
            None => self.open = true,
        }
    }

    /// Add `other`, the need of a value `at` bytes past this one.
    fn merge_at(&mut self, at: Option<u64>, other: &Need) {
        let Some(offset) = at else {
            if other.extent > 0 || other.open || !other.slots.is_empty() {
                self.open = true;
            }
            return;
        };
        if other.extent > 0 {
            self.extent = self.extent.max(offset.saturating_add(other.extent));
        }
        self.open |= other.open;
        for (slot, child) in &other.slots {
            self.slots
                .entry(offset.saturating_add(*slot))
                .or_default()
                .merge_at(Some(0), child);
        }
    }
}

/// How a tracked value relates to the object: a pointer to it, or an
/// address-width integer equal to its address, at a constant offset (or an
/// unknown one).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Track {
    Ptr(Option<u64>),
    Addr(Option<u64>),
}

/// The uses of one function's values, indexed once.
struct Uses<'f> {
    func: &'f Function,
    /// Instruction positions using each value.
    at: HashMap<ValueId, Vec<(usize, usize)>>,
    /// Block parameters each value is passed to on some edge.
    flows: HashMap<ValueId, Vec<ValueId>>,
    /// Single-result instructions by result.
    defs: HashMap<ValueId, &'f Inst>,
}

impl<'f> Uses<'f> {
    fn of(func: &'f Function) -> Self {
        let mut at: HashMap<ValueId, Vec<(usize, usize)>> = HashMap::new();
        let mut flows: HashMap<ValueId, Vec<ValueId>> = HashMap::new();
        let mut defs = HashMap::new();
        let params: HashMap<BlockId, &[(ValueId, Ty)]> = func
            .blocks
            .iter()
            .map(|b| (b.id, b.params.as_slice()))
            .collect();
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                node.inst.visit_value_operands(|v| {
                    let list = at.entry(v).or_default();
                    if list.last() != Some(&(bi, ni)) {
                        list.push((bi, ni));
                    }
                });
                if let [result] = node.results.as_slice() {
                    defs.entry(*result).or_insert(&node.inst);
                }
                for edge in node.inst.successor_edges() {
                    let Some(targets) = params.get(&edge.target) else {
                        continue;
                    };
                    for (arg, (param, _)) in edge.args.iter().zip(targets.iter()) {
                        flows.entry(*arg).or_default().push(*param);
                    }
                }
            }
        }
        Self {
            func,
            at,
            flows,
            defs,
        }
    }

    /// The integer constant `value` is defined as, if any.
    fn constant(&self, value: ValueId) -> Option<i128> {
        match self.defs.get(&value)? {
            Inst::Const {
                value: Constant::Int(c),
                ty,
            } if int_shape(ty, 64).is_some() => Some(*c),
            Inst::Copy { operand, .. } => self.constant(*operand),
            _ => None,
        }
    }
}

fn pointer_like(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

/// The type `ty` points to, when it names one with a size.
fn pointee(ty: &Ty) -> Option<&Ty> {
    match ty {
        Ty::PtrConst(t) | Ty::PtrMut(t) | Ty::Ref(t) | Ty::RefMut(t) => Some(t),
        _ => None,
    }
}

fn offset_by(at: Option<u64>, delta: i128) -> Option<u64> {
    let at = i128::from(at?);
    u64::try_from(at.checked_add(delta)?).ok()
}

/// The access analysis of one module.
struct Analysis<'m> {
    module: &'m Module,
    layout: FsymLayout<'m>,
    pointer_bits: u32,
    limits: HarnessLimits,
    /// Callee parameter needs, by (callee, parameter, as an address integer).
    memo: HashMap<(FuncId, usize, bool), Need>,
    in_progress: HashSet<(FuncId, usize, bool)>,
    visits: usize,
}

impl<'m> Analysis<'m> {
    fn new(module: &'m Module, pointer_bits: u32, limits: HarnessLimits) -> Self {
        Self {
            module,
            layout: FsymLayout::new(module),
            pointer_bits,
            limits,
            memo: HashMap::new(),
            in_progress: HashSet::new(),
            visits: 0,
        }
    }

    fn size(&self, ty: &Ty) -> Option<u64> {
        self.layout.size(ty).ok()
    }

    fn address_int(&self, ty: &Ty) -> bool {
        int_shape(ty, self.pointer_bits).is_some_and(|(bits, _)| bits == self.pointer_bits)
    }

    /// The need of parameter `index` of `func`, followed `depth` calls deep.
    fn param_need(&mut self, func: &Function, index: usize, addr: bool, depth: u32) -> Need {
        let key = (func.id, index, addr);
        if let Some(need) = self.memo.get(&key) {
            return need.clone();
        }
        if func.is_declaration() || !self.in_progress.insert(key) {
            return Need::default();
        }
        let Some(&(param, _)) = func.blocks.first().and_then(|b| b.params.get(index)) else {
            self.in_progress.remove(&key);
            return Need::default();
        };
        let uses = Uses::of(func);
        let start = if addr {
            Track::Addr(Some(0))
        } else {
            Track::Ptr(Some(0))
        };
        let (need, _) = self.value_need(&uses, param, start, depth, 0);
        self.in_progress.remove(&key);
        self.memo.insert(key, need.clone());
        need
    }

    /// The need of `root`, tracked as `start`, and whether it is used as a
    /// pointer (an access, address computation or call through it).
    fn value_need(
        &mut self,
        uses: &Uses<'_>,
        root: ValueId,
        start: Track,
        depth: u32,
        slot_depth: u32,
    ) -> (Need, bool) {
        let mut need = Need::default();
        let mut used = false;
        let mut seen: HashMap<ValueId, Track> = HashMap::new();
        let mut work = VecDeque::from([(root, start)]);
        while let Some((value, track)) = work.pop_front() {
            match seen.get(&value) {
                Some(old) if *old == track => continue,
                Some(old) => {
                    // Reached at two offsets: an unknown one.
                    let merged = match (old, track) {
                        (Track::Ptr(_), Track::Ptr(_)) => Track::Ptr(None),
                        _ => Track::Addr(None),
                    };
                    if *old == merged {
                        continue;
                    }
                    seen.insert(value, merged);
                    work.push_back((value, merged));
                    continue;
                }
                None => {
                    seen.insert(value, track);
                }
            }
            if let Some(params) = uses.flows.get(&value) {
                for param in params {
                    work.push_back((*param, track));
                }
            }
            let Some(sites) = uses.at.get(&value) else {
                continue;
            };
            for &(bi, ni) in sites {
                self.visits += 1;
                if self.visits > self.limits.max_visits {
                    need.open = true;
                    return (need, used);
                }
                let node = &uses.func.blocks[bi].body[ni];
                let result = node.results.first().copied();
                match (&node.inst, track) {
                    (Inst::Copy { .. }, _) => {
                        if let Some(r) = result {
                            work.push_back((r, track));
                        }
                    }
                    (
                        Inst::Select {
                            then_val, else_val, ..
                        },
                        _,
                    ) if *then_val == value || *else_val == value => {
                        if let Some(r) = result {
                            work.push_back((r, track));
                        }
                    }
                    (
                        Inst::Cast {
                            op, dst_ty, src_ty, ..
                        },
                        _,
                    ) => {
                        let Some(r) = result else { continue };
                        match (op, track) {
                            (
                                CastOp::PtrToPtr | CastOp::Bitcast | CastOp::Transmute,
                                Track::Ptr(at),
                            ) if pointer_like(dst_ty) => {
                                work.push_back((r, Track::Ptr(at)));
                            }
                            (CastOp::PtrToInt, Track::Ptr(at)) => {
                                work.push_back((r, Track::Addr(at)));
                            }
                            (CastOp::IntToPtr, Track::Addr(at)) => {
                                used = true;
                                work.push_back((r, Track::Ptr(at)));
                            }
                            (CastOp::Bitcast | CastOp::Transmute, Track::Addr(at))
                                if self.address_int(dst_ty) && self.address_int(src_ty) =>
                            {
                                work.push_back((r, Track::Addr(at)));
                            }
                            (CastOp::Transmute | CastOp::Bitcast, Track::Addr(at))
                                if pointer_like(dst_ty) =>
                            {
                                used = true;
                                work.push_back((r, Track::Ptr(at)));
                            }
                            _ => {}
                        }
                    }
                    (Inst::BinOp { op, lhs, rhs, .. }, Track::Addr(at)) => {
                        let Some(r) = result else { continue };
                        let other = if *lhs == value { *rhs } else { *lhs };
                        let constant = uses.constant(other);
                        let moved = match (op, constant) {
                            (BinOp::Add, Some(c)) => Some(offset_by(at, c)),
                            (BinOp::Add, None) => Some(None),
                            (BinOp::Sub, Some(c)) if *lhs == value => Some(offset_by(at, -c)),
                            _ => None,
                        };
                        if let Some(at) = moved {
                            work.push_back((r, Track::Addr(at)));
                        }
                    }
                    (
                        Inst::GEP {
                            pointee_ty,
                            base,
                            indices,
                            ..
                        },
                        Track::Ptr(at),
                    ) if *base == value => {
                        used = true;
                        let Some(r) = result else { continue };
                        let scale = self.size(pointee_ty);
                        let mut sum = Some(0i128);
                        for index in indices {
                            sum = match (sum, uses.constant(*index)) {
                                (Some(s), Some(c)) => s.checked_add(c),
                                _ => None,
                            };
                        }
                        let delta = match (sum, scale) {
                            (Some(s), Some(scale)) => s.checked_mul(i128::from(scale)),
                            _ => None,
                        };
                        let at = delta.and_then(|d| offset_by(at, d));
                        work.push_back((r, Track::Ptr(at)));
                    }
                    (Inst::Load { ty, ptr, .. }, Track::Ptr(at)) if *ptr == value => {
                        used = true;
                        let size = self.size(ty).unwrap_or(0);
                        need.access(at, size);
                        let (Some(offset), Some(r)) = (at, result) else {
                            continue;
                        };
                        if slot_depth >= self.limits.max_slot_depth {
                            continue;
                        }
                        let child = if pointer_like(ty) {
                            Some(self.value_need(
                                uses,
                                r,
                                Track::Ptr(Some(0)),
                                depth,
                                slot_depth + 1,
                            ))
                        } else if self.address_int(ty) {
                            let (child, deref) = self.value_need(
                                uses,
                                r,
                                Track::Addr(Some(0)),
                                depth,
                                slot_depth + 1,
                            );
                            deref.then_some((child, deref))
                        } else {
                            None
                        };
                        if let Some((child, _)) = child {
                            need.slots
                                .entry(offset)
                                .or_default()
                                .merge_at(Some(0), &child);
                        }
                    }
                    (Inst::Store { ty, ptr, .. }, Track::Ptr(at)) if *ptr == value => {
                        used = true;
                        need.access(at, self.size(ty).unwrap_or(0));
                    }
                    (
                        Inst::MemCopy {
                            dst, src, bytes, ..
                        },
                        Track::Ptr(at),
                    ) if *dst == value || *src == value => {
                        used = true;
                        match uses.constant(*bytes).and_then(|c| u64::try_from(c).ok()) {
                            Some(n) => need.access(at, n),
                            None => need.open = true,
                        }
                    }
                    (Inst::MemSet { dst, bytes, .. }, Track::Ptr(at)) if *dst == value => {
                        used = true;
                        match uses.constant(*bytes).and_then(|c| u64::try_from(c).ok()) {
                            Some(n) => need.access(at, n),
                            None => need.open = true,
                        }
                    }
                    (Inst::Call { callee, args }, _) | (Inst::Invoke { callee, args, .. }, _) => {
                        let module = self.module;
                        let Some(target) = module.function_by_id(*callee) else {
                            continue;
                        };
                        for (index, arg) in args.iter().enumerate() {
                            if *arg != value {
                                continue;
                            }
                            let (addr, at) = match track {
                                Track::Ptr(at) => (false, at),
                                Track::Addr(at) => (true, at),
                            };
                            if !addr {
                                used = true;
                            }
                            if depth >= self.limits.max_call_depth {
                                need.open = true;
                                continue;
                            }
                            let child = self.param_need(target, index, addr, depth + 1);
                            if addr && child == Need::default() {
                                continue;
                            }
                            used = true;
                            need.merge_at(at, &child);
                        }
                    }
                    _ => {}
                }
            }
        }
        (need, used)
    }
}

// ---------------------------------------------------------------------------
// The plan: objects and arguments
// ---------------------------------------------------------------------------

/// A typed scalar in an object's byte image.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Leaf {
    Int(u8),
    Bool,
    Char,
    /// One byte of `str` data: an ASCII letter.
    Letter,
    F32,
    F64,
}

/// One object a driver allocates.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ObjectPlan {
    size: u64,
    /// Typed scalars by offset (pointer slots excluded).
    leaves: Vec<(u64, Leaf)>,
    /// Pointer slots: the offset and the object whose address it holds.
    slots: Vec<(u64, usize)>,
}

/// How one argument is built. `object` is the object an input that does not
/// alias its parameters builds the argument from.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ParamPlan {
    /// A scalar drawn per input (a parameter of the driver).
    Scalar(Ty),
    /// The address of an object, as `ty`.
    Pointer { ty: Ty, object: usize },
    /// A fat pointer to an object of `SLICE_LEN_MAX` elements, with the
    /// input's length.
    Slice {
        ty: Ty,
        metadata_ty: Ty,
        object: usize,
    },
    /// A value of `ty` loaded from an object.
    ByValue { ty: Ty, object: usize },
}

/// An input that binds memory parameters into one shared object.
#[derive(Debug, Clone, PartialEq, Eq)]
struct AliasPlan {
    /// The shared object.
    object: usize,
    /// The parameters bound into it, each with the offset it points at.
    params: Vec<(usize, u64)>,
}

/// One input: the scalar arguments, the objects it allocates and their
/// bytes, the object and offset each memory parameter is built from, and the
/// slice lengths.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Sample {
    scalars: Vec<Option<InterpretValue>>,
    /// Indices into [`Harness::objects`], in allocation order.
    objects: Vec<usize>,
    /// The bytes of each of `objects`, in the same order.
    bytes: Vec<Vec<u8>>,
    /// Per parameter: the object (an index into [`Harness::objects`]) and
    /// the offset a memory parameter's argument is built from.
    bind: Vec<Option<(usize, u64)>>,
    lens: Vec<u64>,
}

/// The inputs of one function and how its runs are driven (module docs).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Harness {
    func: FuncId,
    returns: Vec<Ty>,
    params: Vec<ParamPlan>,
    objects: Vec<ObjectPlan>,
    /// The globals a driver takes the address of before the call: the
    /// function's own (the first `own_globals`), then those the module
    /// functions it reaches through direct calls name.
    globals: Vec<GlobalId>,
    own_globals: usize,
    samples: Vec<Sample>,
    /// How many inputs, at the end of `samples`, alias memory parameters.
    aliased: usize,
    /// Steps a run of this function may take at most.
    fuel_cap: u64,
    /// Extra runs one input may spend narrowing what it reads back.
    read_probes: u32,
}

struct Planner<'m> {
    module: &'m Module,
    layout: FsymLayout<'m>,
    pointer_bits: u32,
    limits: HarnessLimits,
    objects: Vec<ObjectPlan>,
    bytes: u64,
}

impl Planner<'_> {
    fn size(&self, ty: &Ty) -> Result<u64, NotSynthesized> {
        self.layout.size(ty).map_err(|detail| NotSynthesized {
            reason: "no_layout",
            detail,
        })
    }

    /// Plan an object reaching `need` (and laid out as `ty`, when known),
    /// `depth` slots below a parameter; `None` when the limits are reached.
    fn object(&mut self, need: &Need, ty: Option<&Ty>, depth: u32) -> Option<usize> {
        if self.objects.len() >= self.limits.max_objects {
            return None;
        }
        let typed = ty.and_then(|t| self.layout.size(t).ok()).unwrap_or(0);
        let mut size = need.extent.max(typed);
        if need.open || (ty.is_none() && need.extent == 0 && need.slots.is_empty()) {
            size = size.saturating_add(self.limits.open_slack);
        }
        let size = size.max(1);
        if self.bytes.saturating_add(size) > self.limits.max_bytes {
            return None;
        }
        self.bytes += size;
        let index = self.objects.len();
        self.objects.push(ObjectPlan {
            size,
            leaves: Vec::new(),
            slots: Vec::new(),
        });
        let mut leaves = Vec::new();
        let mut typed_slots: Vec<(u64, Option<Ty>)> = Vec::new();
        if let Some(ty) = ty {
            self.walk(ty, 0, &mut leaves, &mut typed_slots, 0);
        }
        let pointer_bytes = u64::from(self.pointer_bits / 8);
        let mut slot_needs: BTreeMap<u64, (Need, Option<Ty>)> = BTreeMap::new();
        for (offset, child) in &need.slots {
            slot_needs.insert(*offset, (child.clone(), None));
        }
        for (offset, child_ty) in typed_slots {
            let entry = slot_needs.entry(offset).or_default();
            if entry.1.is_none() {
                entry.1 = child_ty;
            }
        }
        let mut slots = Vec::new();
        if depth < self.limits.max_slot_depth {
            for (offset, (child_need, child_ty)) in slot_needs {
                if offset.saturating_add(pointer_bytes) > size {
                    continue;
                }
                if let Some(child) = self.object(&child_need, child_ty.as_ref(), depth + 1) {
                    slots.push((offset, child));
                }
            }
        }
        leaves.retain(|(offset, leaf)| {
            let width = leaf_size(*leaf);
            offset.saturating_add(width) <= size
                && !slots
                    .iter()
                    .any(|(s, _)| *offset < s + pointer_bytes && *s < offset + width)
        });
        let object = &mut self.objects[index];
        object.leaves = leaves;
        object.slots = slots;
        Some(index)
    }

    /// The typed scalars and pointer fields of `ty` at `base`.
    fn walk(
        &self,
        ty: &Ty,
        base: u64,
        leaves: &mut Vec<(u64, Leaf)>,
        slots: &mut Vec<(u64, Option<Ty>)>,
        level: u32,
    ) {
        if level > 8 || leaves.len() > 4096 {
            return;
        }
        match ty {
            Ty::Bool => leaves.push((base, Leaf::Bool)),
            Ty::Char => leaves.push((base, Leaf::Char)),
            Ty::F32 => leaves.push((base, Leaf::F32)),
            Ty::F64 => leaves.push((base, Leaf::F64)),
            t if pointer_like(t) => slots.push((base, pointee(t).cloned())),
            // A fat pointer in memory: its data word is a slot whose object is
            // planned untyped and open, its length word a small integer.
            Ty::FatPtr(FatPtrKind::Slice(_) | FatPtrKind::Str) => {
                slots.push((base, None));
                let width = u8::try_from(self.pointer_bits / 8).unwrap_or(4);
                leaves.push((base + u64::from(width), Leaf::Int(width)));
            }
            Ty::Struct(_) | Ty::Tuple(_) => {
                let layout = if matches!(ty, Ty::Struct(_)) {
                    self.layout.struct_layout(ty)
                } else {
                    self.layout.tuple_layout(ty)
                };
                if let Ok(layout) = layout {
                    for (offset, field) in &layout.fields {
                        self.walk(field, base + offset, leaves, slots, level + 1);
                    }
                }
            }
            Ty::Array(elem, count) => {
                let Some(elem_ty) = self.layout_elem(*elem) else {
                    return;
                };
                let Ok(stride) = self.layout.size(&elem_ty) else {
                    return;
                };
                for i in 0..(*count).min(512) {
                    self.walk(&elem_ty, base + i * stride, leaves, slots, level + 1);
                }
            }
            _ => {
                if let Some((bits, _)) = int_shape(ty, self.pointer_bits) {
                    leaves.push((base, Leaf::Int(u8::try_from(bits / 8).unwrap_or(1))));
                }
            }
        }
    }

    fn layout_elem(&self, id: TyId) -> Option<Ty> {
        self.module.ty(id).cloned()
    }
}

fn leaf_size(leaf: Leaf) -> u64 {
    match leaf {
        Leaf::Int(width) => u64::from(width),
        Leaf::Bool | Leaf::Letter => 1,
        Leaf::Char | Leaf::F32 => 4,
        Leaf::F64 => 8,
    }
}

/// What sizes a run's fuel: the instructions (capped) and the loops
/// (retreating CFG edges) of `func` and of the module functions it reaches
/// through direct calls, and whether any of them allocates.
struct StaticSize {
    instructions: u64,
    loops: u64,
    allocates: bool,
}

fn static_size(module: &Module, func: &Function) -> StaticSize {
    let mut seen = HashSet::from([func.id]);
    let mut work = vec![func];
    let mut size = StaticSize {
        instructions: 0,
        loops: 0,
        allocates: false,
    };
    while let Some(f) = work.pop() {
        size.loops += retreating_edges(f);
        for node in f.blocks.iter().flat_map(|b| &b.body) {
            size.instructions += 1;
            size.allocates |= matches!(node.inst, Inst::Alloca { .. } | Inst::HeapAlloc { .. });
            if size.instructions >= STATIC_SIZE_CAP {
                return size;
            }
            if let Inst::Call { callee, .. } | Inst::Invoke { callee, .. } = &node.inst
                && seen.insert(*callee)
                && let Some(g) = module.function_by_id(*callee)
            {
                work.push(g);
            }
        }
    }
    size
}

/// The edges a depth-first walk of `func`'s CFG from its entry meets
/// targeting a block on the current path.
fn retreating_edges(func: &Function) -> u64 {
    let index: HashMap<BlockId, usize> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id, i))
        .collect();
    let succs: Vec<Vec<usize>> = func
        .blocks
        .iter()
        .map(|b| {
            b.body
                .last()
                .map(|n| {
                    n.inst
                        .successor_edges()
                        .iter()
                        .filter_map(|e| index.get(&e.target).copied())
                        .collect()
                })
                .unwrap_or_default()
        })
        .collect();
    let Some(&entry) = index.get(&func.entry) else {
        return 0;
    };
    // 0 unvisited, 1 on the path, 2 done.
    let mut state = vec![0u8; func.blocks.len()];
    let mut stack = vec![(entry, 0usize)];
    state[entry] = 1;
    let mut count = 0;
    while let Some((block, next)) = stack.pop() {
        if let Some(&succ) = succs[block].get(next) {
            stack.push((block, next + 1));
            match state[succ] {
                0 => {
                    state[succ] = 1;
                    stack.push((succ, 0));
                }
                1 => count += 1,
                _ => {}
            }
        } else {
            state[block] = 2;
        }
    }
    count
}

/// Why a parameter of type `ty` has no synthesized value, if it has none.
fn unsynthesizable(ty: &Ty) -> Option<&'static str> {
    Some(match ty {
        Ty::Func(_) => "function_pointer",
        Ty::FatPtr(FatPtrKind::TraitObject { .. }) => "trait_object",
        Ty::FatPtr(FatPtrKind::ContainerLen | FatPtrKind::ContainerVtable) => "unsupported_type",
        Ty::Closure(_) => "closure",
        Ty::Handle(_) => "handle",
        Ty::Storage(_) => "storage_has_no_value",
        Ty::Set(..) | Ty::Sequence(_) | Ty::Record(_) => "collection",
        Ty::Rc(_) | Ty::Never | Ty::Error => "unsupported_type",
        _ => return None,
    })
}

/// The globals `func` names (in order of appearance), then at most `most`
/// more named by the module functions it reaches through direct calls; and
/// how many are `func`'s own.
fn reachable_globals(module: &Module, func: &Function, most: usize) -> (Vec<GlobalId>, usize) {
    let mut globals = Vec::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let Inst::GlobalAddr { global } = node.inst
            && !globals.contains(&global)
        {
            globals.push(global);
        }
    }
    let own = globals.len();
    let mut seen = HashSet::from([func.id]);
    let mut work = vec![func];
    let mut visited = 0u64;
    while let Some(f) = work.pop() {
        for node in f.blocks.iter().flat_map(|b| &b.body) {
            visited += 1;
            if visited >= STATIC_SIZE_CAP || globals.len() >= own + most {
                return (globals, own);
            }
            match &node.inst {
                Inst::GlobalAddr { global } if !globals.contains(global) => globals.push(*global),
                Inst::Call { callee, .. } | Inst::Invoke { callee, .. } => {
                    if seen.insert(*callee)
                        && let Some(g) = module.function_by_id(*callee)
                    {
                        work.push(g);
                    }
                }
                _ => {}
            }
        }
    }
    (globals, own)
}

/// A pointer or slice parameter an aliasing input may bind into a shared
/// object.
struct MemoryParam {
    param: usize,
    need: Need,
    /// The pointee's type, when the parameter's type names one.
    pointee: Option<Ty>,
    /// A slice's element leaves.
    leaves: Vec<(u64, Leaf)>,
}

/// The aliasing inputs of a function whose memory parameters are `memory`,
/// when it has two or more: every one of them at the start of one object,
/// and the second `step` bytes into the first's object (so their accesses
/// overlap partly). An object past the limits is not planned.
fn alias_plans(planner: &mut Planner<'_>, memory: &[MemoryParam]) -> Vec<AliasPlan> {
    let [first, second, ..] = memory else {
        return Vec::new();
    };
    let mut plans = Vec::new();
    let mut shared = Need::default();
    for m in memory {
        shared.merge_at(Some(0), &m.need);
    }
    let ty = memory.iter().find_map(|m| m.pointee.clone());
    if let Some(object) = planner.object(&shared, ty.as_ref(), 0) {
        for m in memory {
            planner.objects[object]
                .leaves
                .extend(m.leaves.iter().copied());
        }
        plans.push(AliasPlan {
            object,
            params: memory.iter().map(|m| (m.param, 0)).collect(),
        });
    }
    let step = if first.need.open {
        4
    } else {
        (first.need.extent / 2).clamp(1, 4)
    };
    let mut overlap = first.need.clone();
    overlap.merge_at(Some(step), &second.need);
    if let Some(object) = planner.object(&overlap, first.pointee.as_ref(), 0) {
        let leaves = &mut planner.objects[object].leaves;
        leaves.extend(first.leaves.iter().copied());
        leaves.extend(second.leaves.iter().map(|&(at, leaf)| (at + step, leaf)));
        plans.push(AliasPlan {
            object,
            params: vec![(first.param, 0), (second.param, step)],
        });
    }
    plans
}

/// `root` and every object its pointer slots reach, parents first.
fn subtree(objects: &[ObjectPlan], root: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut work = vec![root];
    while let Some(object) = work.pop() {
        if out.contains(&object) || object >= objects.len() {
            continue;
        }
        out.push(object);
        work.extend(objects[object].slots.iter().rev().map(|&(_, child)| child));
    }
    out
}

impl Harness {
    /// The inputs of `func` (resolved against `module`): `count` seeded ones.
    pub fn build(
        module: &Module,
        func: &Function,
        pointer_bits: u32,
        count: usize,
        seed: u64,
        budget: DifferentialBudget,
        limits: HarnessLimits,
    ) -> Result<Self, NotSynthesized> {
        let signature = module.func_type(func.ty).ok_or_else(|| NotSynthesized {
            reason: "no_signature",
            detail: format!("function type {} is not in the module", func.ty),
        })?;
        let size = static_size(module, func);
        // The interpreter keeps every allocation a run makes and resolves an
        // address against all of them, so a loop that allocates (in its body
        // or a callee's) makes each step dearer the longer the run: such a
        // run gets the smaller cap.
        let most = if size.loops > 0 && size.allocates {
            budget.max_fuel_per_allocating_loop
        } else {
            budget.max_fuel_per_run
        };
        let fuel_cap = size
            .instructions
            .saturating_mul(budget.fuel_per_instruction)
            .saturating_mul(size.loops.saturating_add(1))
            .clamp(budget.fuel_per_run, most.max(budget.fuel_per_run));
        let (globals, own_globals) = reachable_globals(module, func, limits.max_reached_globals);
        let mut harness = Self {
            func: func.id,
            returns: signature.returns.clone(),
            params: Vec::new(),
            objects: Vec::new(),
            globals,
            own_globals,
            samples: Vec::new(),
            aliased: 0,
            fuel_cap,
            read_probes: limits.max_read_probes,
        };
        if let Some(inputs) = seeded_inputs(module, func, pointer_bits, count, seed) {
            harness.params = signature
                .params
                .iter()
                .cloned()
                .map(ParamPlan::Scalar)
                .collect();
            harness.samples = inputs
                .into_iter()
                .map(|args| Sample {
                    bind: vec![None; args.len()],
                    scalars: args.into_iter().map(Some).collect(),
                    objects: Vec::new(),
                    bytes: Vec::new(),
                    lens: Vec::new(),
                })
                .collect();
            return Ok(harness);
        }
        if signature.is_vararg {
            return Err(NotSynthesized {
                reason: "unsupported_type",
                detail: "a variadic signature".to_string(),
            });
        }
        if let Some(ty) = signature
            .params
            .iter()
            .find(|t| unsynthesizable(t).is_some())
        {
            return Err(NotSynthesized {
                reason: unsynthesizable(ty).unwrap_or("unsupported_type"),
                detail: format!("parameter of type {ty}"),
            });
        }
        let mut analysis = Analysis::new(module, pointer_bits, limits);
        let mut planner = Planner {
            module,
            layout: FsymLayout::new(module),
            pointer_bits,
            limits,
            objects: Vec::new(),
            bytes: 0,
        };
        let too_large = || NotSynthesized {
            reason: "too_large",
            detail: format!(
                "the inputs need more than {} objects or {} bytes",
                limits.max_objects, limits.max_bytes
            ),
        };
        let mut params = Vec::with_capacity(signature.params.len());
        let mut memory: Vec<MemoryParam> = Vec::new();
        for (index, ty) in signature.params.iter().enumerate() {
            let plan = if int_shape(ty, pointer_bits).is_some()
                || matches!(ty, Ty::Bool | Ty::F32 | Ty::F64)
            {
                ParamPlan::Scalar(ty.clone())
            } else if pointer_like(ty) {
                let need = analysis.param_need(func, index, false, 0);
                let object = planner
                    .object(&need, pointee(ty), 0)
                    .ok_or_else(too_large)?;
                memory.push(MemoryParam {
                    param: index,
                    need,
                    pointee: pointee(ty).cloned(),
                    leaves: Vec::new(),
                });
                ParamPlan::Pointer {
                    ty: ty.clone(),
                    object,
                }
            } else if let Ty::FatPtr(kind @ (FatPtrKind::Slice(_) | FatPtrKind::Str)) = ty {
                let metadata_ty = kind
                    .metadata_ty(pointer_bits)
                    .ok_or_else(|| NotSynthesized {
                        reason: "unsupported_type",
                        detail: format!("{ty} has no length type"),
                    })?;
                let element = match kind {
                    FatPtrKind::Slice(elem) => {
                        planner.layout_elem(*elem).ok_or_else(|| NotSynthesized {
                            reason: "no_layout",
                            detail: format!("slice element type {elem} is not in the module"),
                        })?
                    }
                    _ => Ty::U8,
                };
                let stride = planner.size(&element)?;
                let need = Need {
                    extent: stride.saturating_mul(SLICE_LEN_MAX),
                    ..Need::default()
                };
                let object = planner.object(&need, None, 0).ok_or_else(too_large)?;
                // The element layout fills the object, element by element (a
                // pointer element is left as fill: it gets no object); `str`
                // data is ASCII letters.
                let mut leaves = Vec::new();
                if matches!(kind, FatPtrKind::Str) {
                    leaves.extend((0..SLICE_LEN_MAX).map(|i| (i, Leaf::Letter)));
                } else {
                    let mut pointers = Vec::new();
                    for i in 0..SLICE_LEN_MAX {
                        planner.walk(&element, i * stride, &mut leaves, &mut pointers, 0);
                    }
                }
                planner.objects[object].leaves = leaves.clone();
                memory.push(MemoryParam {
                    param: index,
                    need,
                    pointee: None,
                    leaves,
                });
                ParamPlan::Slice {
                    ty: ty.clone(),
                    metadata_ty,
                    object,
                }
            } else {
                planner.size(ty)?;
                let object = planner
                    .object(&Need::default(), Some(ty), 0)
                    .ok_or_else(too_large)?;
                ParamPlan::ByValue {
                    ty: ty.clone(),
                    object,
                }
            };
            params.push(plan);
        }
        harness.params = params;
        let unaliased = planner.objects.len();
        let aliases = alias_plans(&mut planner, &memory);
        harness.objects = planner.objects;
        let mut state = seed ^ 0x6a09_e667_f3bc_c908;
        let objects: Vec<usize> = (0..unaliased).collect();
        let bind: Vec<Option<(usize, u64)>> = harness
            .params
            .iter()
            .map(|plan| match plan {
                ParamPlan::Scalar(_) => None,
                ParamPlan::Pointer { object, .. }
                | ParamPlan::Slice { object, .. }
                | ParamPlan::ByValue { object, .. } => Some((*object, 0)),
            })
            .collect();
        for sample in 0..count {
            let input = harness.sample(sample, pointer_bits, &mut state, &objects, &bind);
            harness.samples.push(input);
        }
        // The aliasing inputs allocate the shared object in place of the
        // objects of the parameters bound into it.
        for (n, alias) in aliases.iter().enumerate() {
            let mut replaced = HashSet::new();
            let mut bind = bind.clone();
            for &(param, offset) in &alias.params {
                if let Some((object, _)) = bind[param] {
                    replaced.extend(subtree(&harness.objects, object));
                }
                bind[param] = Some((alias.object, offset));
            }
            let objects: Vec<usize> = (0..unaliased)
                .filter(|o| !replaced.contains(o))
                .chain(subtree(&harness.objects, alias.object))
                .collect();
            let input = harness.sample(count + n, pointer_bits, &mut state, &objects, &bind);
            harness.samples.push(input);
        }
        harness.aliased = aliases.len();
        Ok(harness)
    }

    /// Input `sample`'s scalars, objects with their bytes, bindings and
    /// lengths.
    fn sample(
        &self,
        sample: usize,
        pointer_bits: u32,
        state: &mut u64,
        objects: &[usize],
        bind: &[Option<(usize, u64)>],
    ) -> Sample {
        let mut scalars = Vec::with_capacity(self.params.len());
        let mut lens = Vec::with_capacity(self.params.len());
        for plan in &self.params {
            scalars.push(match plan {
                ParamPlan::Scalar(ty) => super::sample_value(ty, pointer_bits, sample, state),
                _ => None,
            });
            lens.push(SLICE_LENS[sample % SLICE_LENS.len()]);
        }
        let bytes = objects
            .iter()
            .map(|&object| fill(&self.objects[object], sample, state))
            .collect();
        Sample {
            scalars,
            objects: objects.to_vec(),
            bytes,
            bind: bind.to_vec(),
            lens,
        }
    }

    /// The number of inputs.
    pub fn inputs(&self) -> usize {
        self.samples.len()
    }

    /// How many of the inputs (the last ones) bind two or more memory
    /// parameters into one object.
    pub fn aliased_inputs(&self) -> usize {
        self.aliased
    }

    /// Whether input `sample` binds memory parameters into one object.
    pub fn is_aliased(&self, sample: usize) -> bool {
        sample + self.aliased >= self.samples.len() && sample < self.samples.len()
    }

    /// Whether the function has a parameter that is not a scalar (its inputs
    /// are memory a driver builds).
    pub fn driven(&self) -> bool {
        self.params
            .iter()
            .any(|p| !matches!(p, ParamPlan::Scalar(_)))
    }

    /// The globals a driver takes the address of before the call, the
    /// function's own first.
    pub fn globals(&self) -> usize {
        self.globals.len()
    }

    /// The most steps one run of the function may take.
    pub fn fuel_cap(&self) -> u64 {
        self.fuel_cap
    }

    /// The objects one input allocates.
    pub fn objects(&self) -> usize {
        self.objects.len()
    }
}

/// The bytes of `object` for input `sample`: words of the sample's pattern,
/// then every typed scalar.
fn fill(object: &ObjectPlan, sample: usize, state: &mut u64) -> Vec<u8> {
    let size = usize::try_from(object.size).unwrap_or(0);
    let mut bytes = vec![0u8; size];
    let mode = sample % 8;
    let small = |state: &mut u64| -> u8 { (splitmix(state) % 8) as u8 };
    match mode {
        0 => {}
        1 => {
            for word in bytes.chunks_mut(4) {
                word[0] = 1;
            }
        }
        7 => {
            for byte in &mut bytes {
                *byte = (splitmix(state) & 0xff) as u8;
            }
        }
        _ => {
            for word in bytes.chunks_mut(4) {
                word[0] = small(state);
            }
        }
    }
    for &(offset, leaf) in &object.leaves {
        let at = usize::try_from(offset).unwrap_or(usize::MAX);
        let value: u64 = match (leaf, mode) {
            (_, 0) => 0,
            (Leaf::Bool, 1) => 1,
            (Leaf::Bool, _) => splitmix(state) & 1,
            (Leaf::Char | Leaf::Letter, _) => u64::from(b'a') + splitmix(state) % 26,
            (Leaf::F32, _) => u64::from(
                [1.0f32, -1.5, 3.25, 0.5, -0.0, 1.0e10][(splitmix(state) % 6) as usize].to_bits(),
            ),
            (Leaf::F64, _) => {
                [1.0f64, -1.5, 3.25, 0.5, -0.0, 1.0e10][(splitmix(state) % 6) as usize].to_bits()
            }
            (Leaf::Int(_), 1) => 1,
            (Leaf::Int(width), 7) => {
                let raw = splitmix(state);
                if width >= 8 {
                    raw
                } else {
                    raw & ((1u64 << (8 * width)) - 1)
                }
            }
            (Leaf::Int(_), _) => small(state).into(),
        };
        let width = usize::try_from(leaf_size(leaf)).unwrap_or(0).min(8);
        if let Some(target) = bytes.get_mut(at..at.saturating_add(width)) {
            target.copy_from_slice(&value.to_le_bytes()[..width]);
        }
    }
    bytes
}

// ---------------------------------------------------------------------------
// Drivers
// ---------------------------------------------------------------------------

/// The bytes a driver reads back after the call: per object of the input
/// (in its allocation order), disjoint `(start, length)` segments in
/// increasing order, none empty.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ReadPlan(pub(super) Vec<Vec<(u64, u64)>>);

impl ReadPlan {
    /// The bytes read.
    pub fn bytes(&self) -> u64 {
        self.0.iter().flatten().map(|&(_, len)| len).sum()
    }

    fn segments(&self) -> usize {
        self.0.iter().map(Vec::len).sum()
    }

    /// The first object (in reading order) whose segments hold byte `at`,
    /// and that segment.
    fn holding(&self, at: u64) -> Option<(usize, usize)> {
        self.0.iter().enumerate().find_map(|(object, segments)| {
            segments
                .iter()
                .position(|&(start, len)| start <= at && at < start + len)
                .map(|segment| (object, segment))
        })
    }

    /// Stop reading byte `at` (and the rest of its 4-byte word) in the first
    /// object that reads it; `false` when none does.
    pub(super) fn punch(&mut self, at: u64) -> bool {
        let Some((object, segment)) = self.holding(at) else {
            return false;
        };
        let segments = &mut self.0[object];
        let (start, len) = segments[segment];
        let end = start + len;
        let resume = ((at / 4 + 1) * 4).min(end);
        let mut parts = Vec::with_capacity(2);
        if at > start {
            parts.push((start, at - start));
        }
        if resume < end {
            parts.push((resume, end - resume));
        }
        segments.splice(segment..=segment, parts);
        true
    }

    /// What a read that failed first at byte `at` proves initialised: every
    /// object before the first one reading `at` (each was read whole before
    /// the failure), and that object's segments below `at` (whichever object
    /// failed, its bytes below `at` in reading order were initialised).
    pub(super) fn proven_before(&self, at: u64) -> Option<Self> {
        let (object, _) = self.holding(at)?;
        let mut proven = self.clone();
        for (index, segments) in proven.0.iter_mut().enumerate() {
            if index > object {
                segments.clear();
            } else if index == object {
                segments.retain(|&(start, _)| start < at);
                if let Some(last) = segments.last_mut() {
                    last.1 = last.1.min(at - last.0);
                }
            }
        }
        Some(proven)
    }
}

/// The byte offset a read-back load reports as its first uninitialised
/// byte.
pub(super) fn uninit_offset(message: &str) -> Option<u64> {
    let (_, rest) = message.split_once("reading uninitialized byte at offset ")?;
    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
}

/// What one input's runs read: the globals the driver takes the address of
/// before the call (a prefix of [`Harness::globals`]) and the bytes it reads
/// back after it. A candidate runs each input with its source's reading.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Reading {
    globals: usize,
    plan: ReadPlan,
    /// The plan was narrowed below the whole objects.
    narrowed: bool,
}

impl Reading {
    /// The bytes read back after the call.
    pub fn bytes(&self) -> u64 {
        self.plan.bytes()
    }

    /// Whether the plan reads less than every byte of every object (the
    /// function left some uninitialised).
    pub fn narrowed(&self) -> bool {
        self.narrowed
    }
}

/// What a driver does after building the arguments.
#[derive(Debug, Clone, Copy)]
enum DriverKind<'p> {
    /// Nothing: it returns once the arguments are built.
    Prefix,
    /// Call the function and return its results, the bytes the plan reads
    /// and the marker.
    Call(&'p ReadPlan),
}

/// Builds one driver body, numbering values from 0.
struct Emitter {
    body: Vec<InstrNode>,
    next: u32,
}

impl Emitter {
    fn fresh(&mut self) -> ValueId {
        let value = ValueId::new(self.next);
        self.next += 1;
        value
    }

    fn emit(&mut self, inst: Inst) -> ValueId {
        let value = self.fresh();
        self.body.push(InstrNode::new(inst).with_result(value));
        value
    }

    fn effect(&mut self, inst: Inst) {
        self.body.push(InstrNode::new(inst));
    }

    fn effect_with(&mut self, inst: Inst, results: usize) -> Vec<ValueId> {
        let values: Vec<ValueId> = (0..results).map(|_| self.fresh()).collect();
        self.body
            .push(InstrNode::new(inst).with_results(values.iter().copied()));
        values
    }

    fn usize_const(&mut self, value: u64) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::Usize,
            value: Constant::Int(i128::from(value)),
        })
    }

    /// `base + offset` bytes.
    fn offset(&mut self, base: ValueId, offset: u64) -> ValueId {
        if offset == 0 {
            return base;
        }
        let at = self.usize_const(offset);
        self.emit(Inst::GEP {
            pointee_ty: Ty::U8,
            base,
            indices: vec![at],
            inbounds: false,
        })
    }
}

/// Run `body` against `module` with a `u8` type entry (the type of the bytes
/// a driver writes and reads), and remove what was added again.
fn with_u8<R>(module: &mut Module, body: impl FnOnce(&mut Module, TyId) -> R) -> R {
    let types = module.types.len();
    let u8_ty = match module.types.iter().position(|t| *t == Ty::U8) {
        Some(index) => TyId::new(u32::try_from(index).unwrap_or(u32::MAX)),
        None => {
            module.types.push(Ty::U8);
            TyId::new(u32::try_from(types).unwrap_or(u32::MAX))
        }
    };
    let result = body(module, u8_ty);
    module.types.truncate(types);
    result
}

impl Harness {
    /// The driver of input `sample`, of `kind`, taking the address of the
    /// first `globals` globals, as a function of type `ty_id` (the returned
    /// signature): its parameters are the scalar arguments.
    fn driver(
        &self,
        module: &Module,
        u8_ty: TyId,
        ty_id: FuncTyId,
        sample: usize,
        kind: DriverKind<'_>,
        globals: usize,
    ) -> (Function, FuncTy) {
        let input = &self.samples[sample];
        let mut e = Emitter {
            body: Vec::new(),
            next: 0,
        };
        let mut block_params = Vec::new();
        let mut scalars = vec![None; self.params.len()];
        for (index, plan) in self.params.iter().enumerate() {
            if let ParamPlan::Scalar(ty) = plan {
                let value = e.fresh();
                block_params.push((value, ty.clone()));
                scalars[index] = Some(value);
            }
        }
        let mut at: HashMap<usize, ValueId> = HashMap::new();
        for &object in &input.objects {
            let address = e.emit(Inst::Alloca {
                ty: Ty::Array(u8_ty, self.objects[object].size),
                count: None,
                align: Some(OBJECT_ALIGN),
            });
            at.insert(object, address);
        }
        for (k, &object) in input.objects.iter().enumerate() {
            let plan = &self.objects[object];
            let array = Ty::Array(u8_ty, plan.size);
            let bytes = e.emit(Inst::Const {
                ty: array.clone(),
                value: Constant::Bytes {
                    data: input.bytes[k].clone(),
                    utf8: false,
                },
            });
            e.effect(Inst::Store {
                ty: array,
                ptr: at[&object],
                value: bytes,
                volatile: false,
                align: Some(1),
            });
            for &(offset, child) in &plan.slots {
                let Some(&child) = at.get(&child) else {
                    continue;
                };
                let slot = e.offset(at[&object], offset);
                e.effect(Inst::Store {
                    ty: Ty::Ptr,
                    ptr: slot,
                    value: child,
                    volatile: false,
                    align: Some(1),
                });
            }
        }
        for &global in self.globals.iter().take(globals) {
            if module.globals.get(global.as_usize()).is_some() {
                e.emit(Inst::GlobalAddr { global });
            }
        }
        let mut args = Vec::with_capacity(self.params.len());
        for (index, plan) in self.params.iter().enumerate() {
            let bound = |object: usize| input.bind[index].unwrap_or((object, 0));
            let arg = match plan {
                ParamPlan::Scalar(_) => scalars[index].unwrap_or_else(|| ValueId::new(0)),
                ParamPlan::Pointer { ty, object } => {
                    let (object, offset) = bound(*object);
                    let address = e.offset(at[&object], offset);
                    if *ty == Ty::Ptr {
                        address
                    } else {
                        e.emit(Inst::Cast {
                            op: CastOp::PtrToPtr,
                            src_ty: Ty::Ptr,
                            dst_ty: ty.clone(),
                            operand: address,
                        })
                    }
                }
                ParamPlan::Slice {
                    ty,
                    metadata_ty,
                    object,
                } => {
                    let (object, offset) = bound(*object);
                    let data = e.offset(at[&object], offset);
                    let len = e.emit(Inst::Const {
                        ty: metadata_ty.clone(),
                        value: Constant::Int(i128::from(input.lens[index])),
                    });
                    e.emit(Inst::PtrFromParts {
                        ptr_ty: ty.clone(),
                        metadata_ty: metadata_ty.clone(),
                        data,
                        metadata: len,
                    })
                }
                ParamPlan::ByValue { ty, object } => {
                    let (object, offset) = bound(*object);
                    let address = e.offset(at[&object], offset);
                    e.emit(Inst::Load {
                        ty: ty.clone(),
                        ptr: address,
                        volatile: false,
                        align: Some(1),
                    })
                }
            };
            args.push(arg);
        }
        let returns = match kind {
            DriverKind::Prefix => {
                e.effect(Inst::Return { values: Vec::new() });
                Vec::new()
            }
            DriverKind::Call(plan) => {
                let marker = e.emit(Inst::Alloca {
                    ty: Ty::U8,
                    count: None,
                    align: Some(1),
                });
                let mut values = e.effect_with(
                    Inst::Call {
                        callee: self.func,
                        args,
                    },
                    self.returns.len(),
                );
                let mut returns = self.returns.clone();
                for (k, segments) in plan.0.iter().enumerate() {
                    let Some(&base) = input.objects.get(k).and_then(|o| at.get(o)) else {
                        continue;
                    };
                    for &(start, len) in segments {
                        let address = e.offset(base, start);
                        let ty = Ty::Array(u8_ty, len);
                        values.push(e.emit(Inst::Load {
                            ty: ty.clone(),
                            ptr: address,
                            volatile: false,
                            align: Some(1),
                        }));
                        returns.push(ty);
                    }
                }
                values.push(marker);
                returns.push(Ty::Ptr);
                e.effect(Inst::Return { values });
                returns
            }
        };
        let id = FuncId::new(u32::try_from(module.functions.len()).unwrap_or(u32::MAX));
        let mut driver = Function::new(id, "__trust_cg_irmid_tv_driver", ty_id, BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params = block_params.clone();
        block.body = e.body;
        driver.blocks.push(block);
        let signature = FuncTy {
            params: block_params.into_iter().map(|(_, ty)| ty).collect(),
            returns,
            abi: None,
            is_vararg: false,
        };
        (driver, signature)
    }

    /// The scalar arguments of input `sample`, in parameter order.
    fn scalar_args(&self, sample: usize) -> Vec<InterpretValue> {
        self.params
            .iter()
            .zip(&self.samples[sample].scalars)
            .filter(|(plan, _)| matches!(plan, ParamPlan::Scalar(_)))
            .map(|(_, value)| value.clone().unwrap_or_else(|| InterpretValue::bool(false)))
            .collect()
    }

    /// Run input `sample`'s driver of `kind` up the fuel ladder from `start`,
    /// its signature installed in `module` for the length of the run.
    #[allow(clippy::too_many_arguments)]
    fn run_driver(
        &self,
        module: &mut Module,
        u8_ty: TyId,
        sample: usize,
        kind: DriverKind<'_>,
        globals: usize,
        start: u64,
        budget: DifferentialBudget,
    ) -> Run {
        let ty_id = FuncTyId::new(u32::try_from(module.func_types.len()).unwrap_or(u32::MAX));
        let (driver, signature) = self.driver(module, u8_ty, ty_id, sample, kind, globals);
        module.func_types.push(signature);
        let args = self.scalar_args(sample);
        let run = run_ladder(
            module,
            &driver,
            &args,
            start,
            self.fuel_cap,
            budget.max_call_depth,
        );
        module.func_types.pop();
        run
    }

    /// The plan that reads every byte of every object of input `sample`.
    fn whole(&self, sample: usize) -> ReadPlan {
        ReadPlan(
            self.samples[sample]
                .objects
                .iter()
                .map(|&object| vec![(0, self.objects[object].size)])
                .collect(),
        )
    }

    /// How many of [`Self::globals`] a driver can take the address of
    /// (materializing their initializers): all, else the function's own,
    /// else none. Charges `steps_left`.
    fn materializable_globals(
        &self,
        module: &mut Module,
        budget: DifferentialBudget,
        steps_left: &mut u64,
    ) -> usize {
        for count in [self.globals.len(), self.own_globals] {
            if count == 0 {
                return 0;
            }
            let ty_id = FuncTyId::new(u32::try_from(module.func_types.len()).unwrap_or(u32::MAX));
            module.func_types.push(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                abi: None,
                is_vararg: false,
            });
            let mut e = Emitter {
                body: Vec::new(),
                next: 0,
            };
            for &global in self.globals.iter().take(count) {
                if module.globals.get(global.as_usize()).is_some() {
                    e.emit(Inst::GlobalAddr { global });
                }
            }
            e.effect(Inst::Return { values: Vec::new() });
            let id = FuncId::new(u32::try_from(module.functions.len()).unwrap_or(u32::MAX));
            let mut driver =
                Function::new(id, "__trust_cg_irmid_tv_globals", ty_id, BlockId::new(0));
            let mut block = Block::new(BlockId::new(0));
            block.body = e.body;
            driver.blocks.push(block);
            let run = run_ladder(
                module,
                &driver,
                &[],
                FUEL_LADDER_START,
                self.fuel_cap,
                budget.max_call_depth,
            );
            module.func_types.pop();
            *steps_left = steps_left.saturating_sub(run.charged);
            if matches!(run.result, Some(Ok(ref done)) if done.host_calls == 0) {
                return count;
            }
        }
        0
    }
}

// ---------------------------------------------------------------------------
// Runs and their outcomes
// ---------------------------------------------------------------------------

/// How one input ended for one body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InputOutcome {
    /// The function returned: its results and the bytes its reading reads
    /// back after the call (pointers renamed, see the module docs).
    Returned {
        results: Vec<InterpretValue>,
        memory: Vec<InterpretValue>,
    },
    /// A check failed: the structured panic and its message.
    Panicked(Option<Box<InterpretPanic>>, String),
    /// Undefined behaviour, or an `assume` the input violates (the
    /// refinement rule excludes the input).
    Undefined,
    /// The driver's prefix raised undefined behaviour: the input is not a
    /// value of the parameter types.
    Invalid,
    /// The interpreter could not finish the run: why (see [`not_executed`]).
    NotExecuted(&'static str),
    /// Not run: the module's step budget was spent.
    OverBudget,
}

/// What a compared input observed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Observed {
    /// Only that both returned, with no result and no memory read back:
    /// nothing a rewrite could change except whether the run finishes.
    Termination,
    /// The results, or the structured panic.
    Results,
    /// The results and bytes of the memory the input provided.
    Memory,
}

impl InputOutcome {
    /// Whether the run finished on a defined input (it can be compared).
    pub fn finished(&self) -> bool {
        matches!(
            self,
            InputOutcome::Returned { .. } | InputOutcome::Panicked(..)
        )
    }

    /// What a finished run observed.
    pub fn observed(&self) -> Option<Observed> {
        match self {
            InputOutcome::Returned { memory, .. } if !memory.is_empty() => Some(Observed::Memory),
            InputOutcome::Returned { results, .. } if !results.is_empty() => {
                Some(Observed::Results)
            }
            InputOutcome::Returned { .. } => Some(Observed::Termination),
            InputOutcome::Panicked(..) => Some(Observed::Results),
            _ => None,
        }
    }

    fn describe(&self) -> String {
        match self {
            InputOutcome::Returned { results, memory } => format!(
                "returned {} value(s) and {} memory segment(s)",
                results.len(),
                memory.len()
            ),
            InputOutcome::Panicked(_, message) => format!("panicked ({message})"),
            InputOutcome::Undefined => "raised undefined behaviour".to_string(),
            InputOutcome::Invalid => "is not a valid input".to_string(),
            InputOutcome::NotExecuted(code) => format!("did not finish ({code})"),
            InputOutcome::OverBudget => "was not run (budget)".to_string(),
        }
    }
}

/// The stable reason a run the interpreter could not finish did not finish:
/// the error code, refined for a call to a declaration (`call_to_declaration`)
/// and the call depth (`call_depth`).
pub fn not_executed(error: &InterpretError) -> &'static str {
    match error.code {
        InterpretErrorCode::UnsupportedCall if error.message.contains("bodyless declaration") => {
            "call_to_declaration"
        }
        InterpretErrorCode::OutOfFuel if error.message.contains("call depth") => "call_depth",
        code => code.as_str(),
    }
}

/// One finished or failed run, with the steps charged to it.
struct Run {
    /// `None` when the interpreter itself panicked.
    result: Option<Result<InterpretOutcome, InterpretError>>,
    charged: u64,
    /// The fuel of the rung it ended at.
    rung: u64,
}

impl Run {
    /// The message of the error the run ended with.
    fn error(&self) -> Option<&str> {
        match &self.result {
            Some(Err(error)) => Some(&error.message),
            _ => None,
        }
    }
}

/// Run `driver` (or `func` directly on `args`) up the fuel ladder from
/// `start` to `cap`.
fn run_ladder(
    module: &Module,
    entry: &Function,
    args: &[InterpretValue],
    start: u64,
    cap: u64,
    max_call_depth: u64,
) -> Run {
    let mut fuel = start.clamp(1, cap.max(1));
    let mut charged = 0u64;
    loop {
        let options = InterpretOptions {
            fuel,
            max_call_depth,
            ..InterpretOptions::default()
        };
        let interpreter = Interpreter::with_module(module).with_options(options);
        let result = catch_unwind(AssertUnwindSafe(|| {
            interpreter.execute_function(entry, args.iter().cloned())
        }))
        .ok();
        match &result {
            None => {
                charged = charged.saturating_add(fuel);
                return Run {
                    result,
                    charged,
                    rung: fuel,
                };
            }
            Some(Ok(done)) => {
                charged = charged.saturating_add(done.steps);
                return Run {
                    result,
                    charged,
                    rung: fuel,
                };
            }
            Some(Err(error))
                if error.code == InterpretErrorCode::OutOfFuel
                    && !error.message.contains("call depth")
                    && fuel < cap =>
            {
                charged = charged.saturating_add(fuel);
                fuel = fuel.saturating_mul(FUEL_LADDER_FACTOR).min(cap);
            }
            Some(Err(_)) => {
                charged = charged.saturating_add(fuel);
                return Run {
                    result,
                    charged,
                    rung: fuel,
                };
            }
        }
    }
}

/// What one input of one body did, and what it cost.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputRun {
    pub outcome: InputOutcome,
    /// Steps charged (an upper bound on the steps executed, module docs).
    pub charged: u64,
    /// The fuel the run finished within (a later body's run starts there).
    pub rung: u64,
    /// What the run read; a candidate runs the input with its source's.
    pub reading: Reading,
}

impl InputRun {
    fn new(outcome: InputOutcome, charged: u64, rung: u64, reading: Reading) -> Self {
        Self {
            outcome,
            charged,
            rung,
            reading,
        }
    }
}

/// Run every input in `inputs` (indices) of `harness` on the body `module`
/// holds for the harness's function, the prefix check included, charging at
/// most `steps_left` before starting each input (the rest are
/// [`InputOutcome::OverBudget`]). `start[i]` is the rung input `i` starts at.
pub fn run_inputs(
    module: &mut Module,
    harness: &Harness,
    inputs: &[usize],
    start: &[u64],
    budget: DifferentialBudget,
    steps_left: &mut u64,
) -> Vec<(usize, InputRun)> {
    with_u8(module, |module, u8_ty| {
        if module.function_by_id(harness.func).is_none() {
            return inputs
                .iter()
                .map(|&i| {
                    let outcome = InputOutcome::NotExecuted("missing_function");
                    (i, InputRun::new(outcome, 0, 0, Reading::default()))
                })
                .collect();
        }
        let globals = if *steps_left == 0 {
            0
        } else {
            harness.materializable_globals(module, budget, steps_left)
        };
        let mut runs = Vec::with_capacity(inputs.len());
        for &i in inputs {
            if *steps_left == 0 {
                let run = InputRun::new(InputOutcome::OverBudget, 0, 0, Reading::default());
                runs.push((i, run));
                continue;
            }
            let start = start
                .get(i)
                .copied()
                .unwrap_or(FUEL_LADDER_START)
                .max(FUEL_LADDER_START);
            let run = harness.run_source(module, u8_ty, i, start, globals, budget);
            *steps_left = steps_left.saturating_sub(run.charged);
            runs.push((i, run));
        }
        runs
    })
}

impl Harness {
    /// Whether input runs go through a driver: the function has a memory
    /// parameter, or the driver takes the address of globals first.
    fn uses_driver(&self, globals: usize) -> bool {
        self.driven() || globals > 0
    }

    /// Run the function directly on input `sample`'s scalars.
    fn run_direct(
        &self,
        module: &Module,
        sample: usize,
        start: u64,
        budget: DifferentialBudget,
    ) -> InputRun {
        let Some(func) = module.function_by_id(self.func) else {
            let outcome = InputOutcome::NotExecuted("missing_function");
            return InputRun::new(outcome, 0, 0, Reading::default());
        };
        let args = self.scalar_args(sample);
        let run = run_ladder(
            module,
            func,
            &args,
            start,
            self.fuel_cap,
            budget.max_call_depth,
        );
        let outcome = classify(&run.result, self.returns.len(), None);
        InputRun::new(outcome, run.charged, run.rung, Reading::default())
    }

    /// The source's run of input `sample`: the prefix check, the call with
    /// every object read back after it and, when that read meets bytes the
    /// function left uninitialised, the narrowing of what is read.
    fn run_source(
        &self,
        module: &mut Module,
        u8_ty: TyId,
        sample: usize,
        start: u64,
        globals: usize,
        budget: DifferentialBudget,
    ) -> InputRun {
        if !self.uses_driver(globals) {
            return self.run_direct(module, sample, start, budget);
        }
        let reading = |plan: ReadPlan, narrowed: bool| Reading {
            globals,
            plan,
            narrowed,
        };
        let mut charged = 0u64;
        if self.driven() {
            // The prefix alone: is this a valid input?
            let run = self.run_driver(
                module,
                u8_ty,
                sample,
                DriverKind::Prefix,
                globals,
                FUEL_LADDER_START,
                budget,
            );
            charged = charged.saturating_add(run.charged);
            let invalid = match &run.result {
                Some(Ok(_)) => None,
                Some(Err(error))
                    if matches!(
                        error.code,
                        InterpretErrorCode::UndefinedBehavior | InterpretErrorCode::AssumeViolated
                    ) =>
                {
                    Some(InputOutcome::Invalid)
                }
                Some(Err(error)) => Some(InputOutcome::NotExecuted(not_executed(error))),
                None => Some(InputOutcome::NotExecuted("interpreter_fault")),
            };
            if let Some(outcome) = invalid {
                return InputRun::new(outcome, charged, 0, Reading::default());
            }
        }
        let whole = self.whole(sample);
        let run = self.run_driver(
            module,
            u8_ty,
            sample,
            DriverKind::Call(&whole),
            globals,
            start,
            budget,
        );
        charged = charged.saturating_add(run.charged);
        let outcome = classify(&run.result, self.returns.len(), Some(whole.segments()));
        if outcome != InputOutcome::Undefined || whole.bytes() == 0 {
            return InputRun::new(outcome, charged, run.rung, reading(whole, false));
        }
        let mut error = run.error().map(str::to_string).unwrap_or_default();
        // Undefined: in the call, or in reading the objects back?
        let none = ReadPlan(vec![Vec::new(); whole.0.len()]);
        let call = self.run_driver(
            module,
            u8_ty,
            sample,
            DriverKind::Call(&none),
            globals,
            run.rung,
            budget,
        );
        charged = charged.saturating_add(call.charged);
        let returned = classify(&call.result, self.returns.len(), Some(0));
        if !matches!(returned, InputOutcome::Returned { .. }) {
            return InputRun::new(returned, charged, call.rung, reading(none, true));
        }
        // The call returned, so the read met a byte the function left
        // uninitialised: stop reading it and read again, while the probes
        // last; then read what the last failure proves initialised.
        let mut plan = whole;
        let mut rung = call.rung;
        for _ in 0..self.read_probes {
            let Some(at) = uninit_offset(&error) else {
                break;
            };
            if !plan.punch(at) {
                break;
            }
            let run = self.run_driver(
                module,
                u8_ty,
                sample,
                DriverKind::Call(&plan),
                globals,
                rung,
                budget,
            );
            charged = charged.saturating_add(run.charged);
            rung = run.rung;
            match classify(&run.result, self.returns.len(), Some(plan.segments())) {
                outcome @ InputOutcome::Returned { .. } => {
                    return InputRun::new(outcome, charged, rung, reading(plan, true));
                }
                InputOutcome::Undefined => {
                    error = run.error().map(str::to_string).unwrap_or_default();
                }
                _ => {
                    error.clear();
                    break;
                }
            }
        }
        if let Some(proven) = uninit_offset(&error).and_then(|at| plan.proven_before(at))
            && proven.bytes() > 0
        {
            let run = self.run_driver(
                module,
                u8_ty,
                sample,
                DriverKind::Call(&proven),
                globals,
                rung,
                budget,
            );
            charged = charged.saturating_add(run.charged);
            let outcome = classify(&run.result, self.returns.len(), Some(proven.segments()));
            if matches!(outcome, InputOutcome::Returned { .. }) {
                return InputRun::new(outcome, charged, run.rung, reading(proven, true));
            }
        }
        InputRun::new(returned, charged, call.rung, reading(none, true))
    }

    /// The candidate's run of input `sample` with its source's `reading`.
    #[allow(clippy::too_many_arguments)]
    fn run_target_one(
        &self,
        module: &mut Module,
        u8_ty: TyId,
        sample: usize,
        start: u64,
        reading: &Reading,
        budget: DifferentialBudget,
    ) -> InputRun {
        if !self.uses_driver(reading.globals) {
            return self.run_direct(module, sample, start, budget);
        }
        let run = self.run_driver(
            module,
            u8_ty,
            sample,
            DriverKind::Call(&reading.plan),
            reading.globals,
            start,
            budget,
        );
        let outcome = classify(
            &run.result,
            self.returns.len(),
            Some(reading.plan.segments()),
        );
        InputRun::new(outcome, run.charged, run.rung, reading.clone())
    }
}

/// The outcome of a finished or failed run. A driver's results end with the
/// marker, after `segments` read-back byte arrays (`None`: a direct run,
/// whose results are the function's alone).
fn classify(
    result: &Option<Result<InterpretOutcome, InterpretError>>,
    returns: usize,
    segments: Option<usize>,
) -> InputOutcome {
    let Some(result) = result else {
        return InputOutcome::NotExecuted("interpreter_fault");
    };
    match result {
        Ok(done) if done.host_calls != 0 => InputOutcome::NotExecuted("host_assisted"),
        Ok(done) => {
            let mut values = done.returns.clone();
            let marker = match segments {
                Some(_) => match values.pop() {
                    Some(InterpretValue {
                        kind: InterpretValueKind::Ptr(p),
                        ..
                    }) => p.allocation,
                    _ => return InputOutcome::NotExecuted("driver_marker"),
                },
                None => 0,
            };
            let arity = match segments {
                Some(segments) => values.len() == returns + segments,
                None => values.len() >= returns,
            };
            if !arity {
                return InputOutcome::NotExecuted("signature_mismatch");
            }
            let mut results = canonical(values, marker);
            let memory = match segments {
                Some(_) => results.split_off(returns),
                None => Vec::new(),
            };
            InputOutcome::Returned { results, memory }
        }
        Err(error) => match error.code {
            InterpretErrorCode::UndefinedBehavior | InterpretErrorCode::AssumeViolated => {
                InputOutcome::Undefined
            }
            InterpretErrorCode::Panic => {
                InputOutcome::Panicked(error.panic.clone(), error.message.clone())
            }
            _ => InputOutcome::NotExecuted(not_executed(error)),
        },
    }
}

/// `values` with every allocation made at or after `marker` renamed by
/// order of first appearance (`u64::MAX`, `u64::MAX - 1`, ...).
fn canonical(values: Vec<InterpretValue>, marker: u64) -> Vec<InterpretValue> {
    let mut names: HashMap<u64, u64> = HashMap::new();
    values
        .into_iter()
        .map(|v| rename(v, marker, &mut names))
        .collect()
}

fn rename(value: InterpretValue, marker: u64, names: &mut HashMap<u64, u64>) -> InterpretValue {
    let InterpretValue { ty, kind } = value;
    let kind = match kind {
        InterpretValueKind::Ptr(p) if p.allocation >= marker => {
            let next = u64::MAX - names.len() as u64;
            let name = *names.entry(p.allocation).or_insert(next);
            InterpretValueKind::Ptr(InterpretPointer {
                allocation: name,
                offset: p.offset,
            })
        }
        InterpretValueKind::Aggregate(fields) => InterpretValueKind::Aggregate(
            fields
                .into_iter()
                .map(|f| rename(f, marker, names))
                .collect(),
        ),
        InterpretValueKind::FatPtr { data, metadata } => InterpretValueKind::FatPtr {
            data: Box::new(rename(*data, marker, names)),
            metadata: Box::new(rename(*metadata, marker, names)),
        },
        InterpretValueKind::Array(items) if items.iter().any(holds_pointer) => {
            InterpretValueKind::Array(ArrayValue::from_vec(
                items
                    .to_vec()
                    .into_iter()
                    .map(|v| rename(v, marker, names))
                    .collect(),
            ))
        }
        other => other,
    };
    InterpretValue { ty, kind }
}

fn holds_pointer(value: &InterpretValue) -> bool {
    match &value.kind {
        InterpretValueKind::Ptr(_) | InterpretValueKind::FatPtr { .. } => true,
        InterpretValueKind::Aggregate(fields) => fields.iter().any(holds_pointer),
        InterpretValueKind::Array(items) => items.iter().any(holds_pointer),
        _ => false,
    }
}

/// The comparison of one input's source and target outcomes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InputVerdict {
    /// Both finished and agree on what they observed.
    Compared { observed: Observed },
    /// The source did not give a comparable outcome: why (the source's
    /// outcome).
    Excluded(InputOutcome),
    /// They disagree.
    Mismatch(String),
}

/// Compare `target` against `source` on one input under the refinement rule.
pub fn compare_input(source: &InputOutcome, target: &InputOutcome) -> InputVerdict {
    let Some(observed) = source.observed() else {
        return InputVerdict::Excluded(source.clone());
    };
    if source == target {
        return InputVerdict::Compared { observed };
    }
    InputVerdict::Mismatch(format!(
        "source {}, target {}",
        source.describe(),
        target.describe()
    ))
}

/// Whether a target run is owed on an input: the source finished it.
pub fn target_needs_run(source: &InputOutcome) -> bool {
    source.finished()
}

/// Run the target body (installed in `module` in place of the source) on
/// the inputs the source finished, each with the source's reading, and
/// compare. `source` holds the source's runs by input index.
pub fn run_target(
    module: &mut Module,
    harness: &Harness,
    source: &[InputRun],
    budget: DifferentialBudget,
    steps_left: &mut u64,
) -> Vec<Option<InputRun>> {
    let inputs: Vec<usize> = (0..source.len())
        .filter(|&i| target_needs_run(&source[i].outcome))
        .collect();
    // A target run is never cut short by the budget: the source finished, so
    // the comparison is owed; its steps are still charged.
    let runs = with_u8(module, |module, u8_ty| {
        inputs
            .iter()
            .map(|&i| {
                let run = harness.run_target_one(
                    module,
                    u8_ty,
                    i,
                    source[i].rung,
                    &source[i].reading,
                    budget,
                );
                (i, run)
            })
            .collect::<Vec<_>>()
    });
    let mut out = vec![None; source.len()];
    for (i, run) in runs {
        *steps_left = steps_left.saturating_sub(run.charged);
        out[i] = Some(run);
    }
    out
}

// ---------------------------------------------------------------------------
// The interpreter's view of the lane's idioms
// ---------------------------------------------------------------------------

/// The type of each value of `func` that this view reads: block parameters,
/// single-result instructions whose result type is a field of the
/// instruction, and call results (the callee's declared returns).
fn view_types(module: &Module, func: &Function) -> HashMap<ValueId, Ty> {
    let mut types = HashMap::new();
    for block in &func.blocks {
        for (value, ty) in &block.params {
            types.insert(*value, ty.clone());
        }
        for node in &block.body {
            if let Inst::Call { callee, .. } = &node.inst {
                let returns = module
                    .function_by_id(*callee)
                    .and_then(|f| module.func_type(f.ty))
                    .map(|t| t.returns.clone())
                    .unwrap_or_default();
                for (value, ty) in node.results.iter().zip(returns) {
                    types.insert(*value, ty);
                }
                continue;
            }
            let [result] = node.results.as_slice() else {
                continue;
            };
            let ty = match &node.inst {
                Inst::Copy { ty, .. }
                | Inst::Load { ty, .. }
                | Inst::Const { ty, .. }
                | Inst::Select { ty, .. }
                | Inst::Undef { ty }
                | Inst::UnOp { ty, .. }
                | Inst::BinOp { ty, .. } => ty.clone(),
                Inst::Cast { dst_ty, .. } => dst_ty.clone(),
                Inst::ICmp { .. } | Inst::FCmp { .. } => Ty::Bool,
                Inst::PtrFromParts { ptr_ty, .. } => ptr_ty.clone(),
                Inst::Alloca { .. }
                | Inst::GEP { .. }
                | Inst::GlobalAddr { .. }
                | Inst::NullPtr
                | Inst::PtrData { .. } => Ty::Ptr,
                _ => continue,
            };
            types.insert(*result, ty);
        }
    }
    types
}

fn same_width_ints(a: &Ty, b: &Ty, pointer_bits: u32) -> bool {
    match (int_shape(a, pointer_bits), int_shape(b, pointer_bits)) {
        (Some((x, _)), Some((y, _))) => x == y && a != b,
        _ => false,
    }
}

/// The unsigned integer type of `bits`.
fn unsigned_of(bits: u32) -> Option<Ty> {
    Some(match bits {
        8 => Ty::U8,
        16 => Ty::U16,
        32 => Ty::U32,
        64 => Ty::U64,
        128 => Ty::U128,
        _ => return None,
    })
}

/// Rewrites one function into the view: new instructions take fresh values.
struct Viewer<'m> {
    module: &'m Module,
    layout: FsymLayout<'m>,
    pointer_bits: u32,
    types: HashMap<ValueId, Ty>,
    /// Each block's parameter types.
    params: HashMap<BlockId, Vec<Ty>>,
    /// The function's declared returns.
    returns: Vec<Ty>,
    next: u32,
    body: Vec<InstrNode>,
    changed: bool,
}

impl Viewer<'_> {
    fn fresh(&mut self, inst: Inst, ty: Ty) -> ValueId {
        let value = ValueId::new(self.next);
        self.next += 1;
        self.types.insert(value, ty);
        self.body.push(InstrNode::new(inst).with_result(value));
        self.changed = true;
        value
    }

    /// `value` as `want`: a bitcast between integers of one width, a
    /// zero-extension of a narrower integer when `widen`, a `ptrtoptr`
    /// between pointer-like types; `value` itself otherwise.
    fn coerce(&mut self, value: ValueId, want: &Ty, widen: bool) -> ValueId {
        let Some(have) = self.types.get(&value).cloned() else {
            return value;
        };
        if &have == want {
            return value;
        }
        let op = if same_width_ints(&have, want, self.pointer_bits) {
            CastOp::Bitcast
        } else if pointer_like(&have) && pointer_like(want) {
            CastOp::PtrToPtr
        } else if widen
            && let (Some((a, _)), Some((b, _))) = (
                int_shape(&have, self.pointer_bits),
                int_shape(want, self.pointer_bits),
            )
            && a < b
        {
            CastOp::ZExt
        } else {
            return value;
        };
        self.fresh(
            Inst::Cast {
                op,
                src_ty: have,
                dst_ty: want.clone(),
                operand: value,
            },
            want.clone(),
        )
    }

    /// The byte offset and type of lane `field` of `ty` (a struct, tuple or
    /// array), by the interpreter's layout.
    fn lane(&self, ty: &Ty, field: u32) -> Option<(u64, Ty)> {
        match ty {
            Ty::Struct(_) => self
                .layout
                .struct_layout(ty)
                .ok()?
                .fields
                .get(field as usize)
                .cloned(),
            Ty::Tuple(_) => self
                .layout
                .tuple_layout(ty)
                .ok()?
                .fields
                .get(field as usize)
                .cloned(),
            Ty::Array(elem, count) if u64::from(field) < *count => {
                let elem = self.module.ty(*elem)?.clone();
                let stride = self.layout.size(&elem).ok()?;
                Some((u64::from(field) * stride, elem))
            }
            _ => None,
        }
    }

    /// The view of `ExtractField { ty, aggregate, field }`, or `None` when
    /// the interpreter reads it as the lane does:
    ///
    /// * over a POINTER operand (the bridge's read-through form), lane
    ///   `field` of the declared aggregate loaded from the pointee;
    /// * over an aggregate whose type IS the declared one (the historical
    ///   spelling), its lane `field` (an array's through the element form);
    /// * over an array in the trust-ir spelling (the declared type is the
    ///   lane's), the element form;
    /// * over an aggregate of another type of the declared one's size (the
    ///   bridge's reinterpretation), lane `field` of the declared aggregate
    ///   read over the operand's bytes.
    fn extract(&mut self, ty: Ty, aggregate: ValueId, field: u32) -> Option<Inst> {
        let operand = self.types.get(&aggregate)?.clone();
        let load = |lane_ty: Ty, at: ValueId| Inst::Load {
            ty: lane_ty,
            ptr: at,
            volatile: false,
            align: Some(1),
        };
        if pointer_like(&operand) {
            if !record(&ty) {
                return None;
            }
            let (offset, lane_ty) = self.lane(&ty, field)?;
            let at = self.byte_address(aggregate, offset);
            return Some(load(lane_ty, at));
        }
        if !record(&operand) {
            return None;
        }
        let own = self.lane(&operand, field);
        let element = |viewer: &mut Self, lane_ty: Ty| {
            let index = viewer.fresh(
                Inst::Const {
                    ty: Ty::Usize,
                    value: Constant::Int(i128::from(field)),
                },
                Ty::Usize,
            );
            Inst::ExtractElement {
                ty: lane_ty,
                array: aggregate,
                index,
            }
        };
        let array = matches!(operand, Ty::Array(..));
        if ty == operand {
            let (_, lane_ty) = own?;
            return Some(if array {
                element(self, lane_ty)
            } else {
                Inst::ExtractField {
                    ty: lane_ty,
                    aggregate,
                    field,
                }
            });
        }
        if own.as_ref().is_some_and(|(_, t)| *t == ty) {
            return array.then(|| element(self, ty));
        }
        if !record(&ty) {
            return None;
        }
        let (size, declared) = (
            self.layout.size(&operand).ok()?,
            self.layout.size(&ty).ok()?,
        );
        let (offset, lane_ty) = self.lane(&ty, field)?;
        if size != declared || size == 0 {
            return None;
        }
        let slot = self.fresh(
            Inst::Alloca {
                ty: operand.clone(),
                count: None,
                align: Some(OBJECT_ALIGN),
            },
            Ty::Ptr,
        );
        self.body.push(InstrNode::new(Inst::Store {
            ty: operand,
            ptr: slot,
            value: aggregate,
            volatile: false,
            align: Some(1),
        }));
        let at = self.byte_address(slot, offset);
        Some(load(lane_ty, at))
    }

    /// A plain access's alignment as the lane reads it: wasm loads and
    /// stores never fault on alignment (the lane's alignment is a hint).
    fn unaligned(&mut self, align: &mut Option<u64>) {
        if *align != Some(1) {
            *align = Some(1);
            self.changed = true;
        }
    }

    /// `value`'s address as a `usize` when it is a pointer; `value` itself
    /// otherwise.
    fn address(&mut self, value: ValueId) -> ValueId {
        match self.types.get(&value).cloned() {
            Some(have) if pointer_like(&have) => self.fresh(
                Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: have,
                    dst_ty: Ty::Usize,
                    operand: value,
                },
                Ty::Usize,
            ),
            _ => value,
        }
    }

    /// A pointer `value` where an aggregate of type `want` is passed or
    /// returned by value: the lane passes such an aggregate by its address,
    /// so the value is the pointee's bytes, loaded as `want`.
    fn by_value(&mut self, value: ValueId, want: &Ty) -> ValueId {
        match self.types.get(&value) {
            Some(have) if pointer_like(have) && record(want) => self.fresh(
                Inst::Load {
                    ty: want.clone(),
                    ptr: value,
                    volatile: false,
                    align: Some(1),
                },
                want.clone(),
            ),
            _ => value,
        }
    }

    fn byte_address(&mut self, base: ValueId, offset: u64) -> ValueId {
        if offset == 0 {
            return base;
        }
        let at = self.fresh(
            Inst::Const {
                ty: Ty::Usize,
                value: Constant::Int(i128::from(offset)),
            },
            Ty::Usize,
        );
        self.fresh(
            Inst::GEP {
                pointee_ty: Ty::U8,
                base,
                indices: vec![at],
                inbounds: false,
            },
            Ty::Ptr,
        )
    }

    /// The view of `node`: pushes its replacement (or itself) onto the body.
    fn node(&mut self, node: &InstrNode) {
        let result = node.results.first().copied();
        let mut inst = node.inst.clone();
        match &mut inst {
            Inst::Copy { ty, operand } => {
                let want = ty.clone();
                *operand = self.coerce(*operand, &want, false);
            }
            Inst::Store {
                ty, value, align, ..
            } => {
                let want = ty.clone();
                *value = self.coerce(*value, &want, false);
                self.unaligned(align);
            }
            Inst::Load { align, .. } => self.unaligned(align),
            Inst::ICmp { ty, lhs, rhs, .. } if pointer_like(ty) => {
                // The lane compares the two addresses.
                *lhs = self.address(*lhs);
                *rhs = self.address(*rhs);
                *ty = Ty::Usize;
                self.changed = true;
            }
            Inst::ICmp { ty, lhs, rhs, .. } => {
                let want = ty.clone();
                *lhs = self.coerce(*lhs, &want, false);
                *rhs = self.coerce(*rhs, &want, false);
            }
            Inst::Select {
                ty,
                then_val,
                else_val,
                ..
            } => {
                let want = ty.clone();
                *then_val = self.coerce(*then_val, &want, false);
                *else_val = self.coerce(*else_val, &want, false);
            }
            Inst::Return { values } => {
                for (value, want) in values.iter_mut().zip(self.returns.clone()) {
                    *value = self.by_value(*value, &want);
                    *value = self.coerce(*value, &want, false);
                }
            }
            Inst::Br { target, args } => {
                let params = self.params.get(target).cloned().unwrap_or_default();
                for (arg, want) in args.iter_mut().zip(&params) {
                    *arg = self.coerce(*arg, want, false);
                }
            }
            Inst::CondBr {
                then_target,
                then_args,
                else_target,
                else_args,
                ..
            } => {
                for (target, args) in [(*then_target, then_args), (*else_target, else_args)] {
                    let params = self.params.get(&target).cloned().unwrap_or_default();
                    for (arg, want) in args.iter_mut().zip(&params) {
                        *arg = self.coerce(*arg, want, false);
                    }
                }
            }
            Inst::BinOp { op, ty, lhs, rhs } if int_shape(ty, self.pointer_bits).is_some() => {
                let want = ty.clone();
                let shift = matches!(
                    op,
                    BinOp::Shl | BinOp::LShr | BinOp::AShr | BinOp::RotL | BinOp::RotR
                );
                *lhs = self.coerce(*lhs, &want, false);
                *rhs = self.coerce(*rhs, &want, shift);
            }
            Inst::Const { ty, value } => match (&*ty, &*value) {
                (Ty::Bool, Constant::Int(n @ (0 | 1))) => {
                    *value = Constant::Bool(*n == 1);
                    self.changed = true;
                }
                (t, Constant::Int(n))
                    if (pointer_like(t) || *t == Ty::I64)
                        && let Some((index, offset)) = global_addr_stub(*n)
                        && (index as usize) < self.module.globals.len() =>
                {
                    // The bridge's global-address stub: the address of
                    // `globals[index] + offset`, as the lane emits it.
                    let t = t.clone();
                    let base = self.fresh(
                        Inst::GlobalAddr {
                            global: GlobalId::new(u32::try_from(index).unwrap_or(u32::MAX)),
                        },
                        Ty::Ptr,
                    );
                    let at = self.byte_address(base, u64::from(offset));
                    inst = Inst::Cast {
                        op: if t == Ty::I64 {
                            CastOp::PtrToInt
                        } else {
                            CastOp::PtrToPtr
                        },
                        src_ty: Ty::Ptr,
                        dst_ty: t,
                        operand: at,
                    };
                    self.changed = true;
                }
                (t, Constant::Int(n)) if pointer_like(t) && *n >= 0 => {
                    let t = t.clone();
                    let n = *n;
                    let address = self.fresh(
                        Inst::Const {
                            ty: Ty::Usize,
                            value: Constant::Int(n),
                        },
                        Ty::Usize,
                    );
                    inst = Inst::Cast {
                        op: CastOp::IntToPtr,
                        src_ty: Ty::Usize,
                        dst_ty: t,
                        operand: address,
                    };
                    self.changed = true;
                }
                (t, Constant::SymbolAddr { symbol, addend }) if pointer_like(t) && *addend >= 0 => {
                    let Some(global) = self.module.globals.iter().position(|g| &g.name == symbol)
                    else {
                        self.body.push(node.clone());
                        return;
                    };
                    let t = t.clone();
                    let addend = u64::try_from(*addend).unwrap_or(0);
                    let base = self.fresh(
                        Inst::GlobalAddr {
                            global: GlobalId::new(u32::try_from(global).unwrap_or(u32::MAX)),
                        },
                        Ty::Ptr,
                    );
                    let at = self.byte_address(base, addend);
                    inst = Inst::Cast {
                        op: CastOp::PtrToPtr,
                        src_ty: Ty::Ptr,
                        dst_ty: t,
                        operand: at,
                    };
                    self.changed = true;
                }
                _ => {}
            },
            Inst::MemSet { bytes, .. } | Inst::MemCopy { bytes, .. } => {
                if let Some((bits, true)) = self
                    .types
                    .get(bytes)
                    .and_then(|t| int_shape(t, self.pointer_bits))
                    && let Some(want) = unsigned_of(bits)
                {
                    *bytes = self.coerce(*bytes, &want, false);
                }
            }
            Inst::Cast {
                op: CastOp::PtrToPtr | CastOp::PtrToInt,
                src_ty,
                operand,
                ..
            } => {
                if let Some(have) = self.types.get(operand)
                    && pointer_like(have)
                    && have != src_ty
                {
                    *src_ty = have.clone();
                    self.changed = true;
                }
            }
            Inst::Call { callee, args } => {
                let params = self
                    .module
                    .function_by_id(*callee)
                    .and_then(|f| self.module.func_type(f.ty))
                    .map(|t| t.params.clone())
                    .unwrap_or_default();
                for (arg, param) in args.iter_mut().zip(&params) {
                    *arg = self.by_value(*arg, param);
                    if self.types.get(arg).is_some_and(pointer_like) && pointer_like(param) {
                        *arg = self.coerce(*arg, param, false);
                    }
                }
            }
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } if self
                .types
                .get(aggregate)
                .is_some_and(|t| t != ty && pointer_like(t)) =>
            {
                // The bridge's write-through form: the lane stores the field
                // through the pointer, and the result is that pointer.
                let Some((offset, lane_ty)) = self.lane(ty, *field) else {
                    self.body.push(node.clone());
                    return;
                };
                let (aggregate, value) = (*aggregate, *value);
                let pointer_ty = self.types.get(&aggregate).cloned().unwrap_or(Ty::Ptr);
                let at = self.byte_address(aggregate, offset);
                let value = self.coerce(value, &lane_ty, false);
                self.body.push(InstrNode::new(Inst::Store {
                    ty: lane_ty,
                    ptr: at,
                    value,
                    volatile: false,
                    align: Some(1),
                }));
                inst = Inst::Copy {
                    ty: pointer_ty,
                    operand: aggregate,
                };
                self.changed = true;
            }
            Inst::ExtractField {
                ty,
                aggregate,
                field,
            } => {
                if let Some(viewed) = self.extract(ty.clone(), *aggregate, *field) {
                    inst = viewed;
                    self.changed = true;
                }
            }
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } if matches!(ty, Ty::Array(..)) && self.types.get(aggregate) == Some(&*ty) => {
                // An array's lane: the interpreter's element form.
                let Some((_, lane_ty)) = self.lane(ty, *field) else {
                    self.body.push(node.clone());
                    return;
                };
                let (ty, aggregate, value) = (ty.clone(), *aggregate, *value);
                let index = self.fresh(
                    Inst::Const {
                        ty: Ty::Usize,
                        value: Constant::Int(i128::from(*field)),
                    },
                    Ty::Usize,
                );
                let value = self.coerce(value, &lane_ty, false);
                inst = Inst::InsertElement {
                    ty,
                    array: aggregate,
                    index,
                    value,
                };
                self.changed = true;
            }
            _ => {}
        }
        if let (Some(r), Some(ty)) = (result, result_type(&inst)) {
            self.types.insert(r, ty);
        }
        let mut out = node.clone();
        out.inst = inst;
        self.body.push(out);
    }
}

/// A struct, tuple or array type.
fn record(ty: &Ty) -> bool {
    matches!(ty, Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(..))
}

fn result_type(inst: &Inst) -> Option<Ty> {
    match inst {
        Inst::Copy { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::Const { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. } => Some(ty.clone()),
        Inst::ExtractField { ty, .. } if !record(ty) => Some(ty.clone()),
        Inst::Cast { dst_ty, .. } => Some(dst_ty.clone()),
        _ => None,
    }
}

/// The view of `func` the differential interprets, or `None` when it is
/// `func` itself (see the module docs, "The interpreter's view").
pub fn interpretable(module: &Module, func: &Function) -> Option<Function> {
    if func.is_declaration() {
        return None;
    }
    let next = func
        .value_ids()
        .map(|v| v.index())
        .max()
        .map_or(0, |m| m.saturating_add(1));
    // An entry parameter declared with another pointer-like type than the
    // signature's takes the signature's (the interpreter checks both).
    let mut func = std::borrow::Cow::Borrowed(func);
    if let Some(signature) = module.func_type(func.ty) {
        let entry = func.blocks.iter().position(|b| b.id == func.entry);
        let differs =
            |(have, want): (&Ty, &Ty)| have != want && pointer_like(have) && pointer_like(want);
        if let Some(entry) = entry
            && func.blocks[entry]
                .params
                .iter()
                .map(|(_, t)| t)
                .zip(&signature.params)
                .any(differs)
        {
            let owned = func.to_mut();
            for ((_, have), want) in owned.blocks[entry].params.iter_mut().zip(&signature.params) {
                if differs((have, want)) {
                    *have = want.clone();
                }
            }
        }
    }
    let entry_changed = matches!(func, std::borrow::Cow::Owned(_));
    let func: &Function = &func;
    let mut viewer = Viewer {
        module,
        layout: FsymLayout::new(module),
        pointer_bits: FsymLayout::new(module).pointer_bits(),
        types: view_types(module, func),
        params: func
            .blocks
            .iter()
            .map(|b| (b.id, b.params.iter().map(|(_, t)| t.clone()).collect()))
            .collect(),
        returns: module
            .func_type(func.ty)
            .map(|t| t.returns.clone())
            .unwrap_or_default(),
        next,
        body: Vec::new(),
        changed: false,
    };
    let mut out = func.clone();
    for block in &mut out.blocks {
        viewer.body = Vec::with_capacity(block.body.len());
        for node in &block.body {
            viewer.node(node);
        }
        block.body = std::mem::take(&mut viewer.body);
    }
    (viewer.changed || entry_changed).then_some(out)
}

/// The bytes the view reserves for a global without an initializer (module
/// docs, the interpreter's view): its real extent is unknown here.
pub(crate) const EXTERN_GLOBAL_RESERVE: u64 = 1 << 20;

/// The tag of the bridge's global-address stub (`trust_cg_codegen::
/// global_stub`): a pointer or `i64` constant whose bits are
/// `0xFADE << 48 | index << 32 | offset` is the address of
/// `globals[index] + offset`.
const GLOBAL_ADDR_STUB_TAG: u64 = 0xFADE;

/// The `(global index, offset)` a global-address stub encodes, if `value` is
/// one (the decoder of `trust_cg_codegen::global_stub`).
pub fn global_addr_stub(value: i128) -> Option<(u64, u32)> {
    let bits = u64::try_from(value).ok()?;
    if bits >> 48 != GLOBAL_ADDR_STUB_TAG {
        return None;
    }
    Some(((bits >> 32) & 0xFFFF, (bits & 0xFFFF_FFFF) as u32))
}

/// Whether `constant` is the address of a global of `module` the
/// interpreter resolves at a typed pointer (`SymbolAddr` naming exactly one
/// global).
fn global_symbol(module: &Module, constant: &Constant) -> bool {
    matches!(constant, Constant::SymbolAddr { symbol, addend }
        if *addend >= 0 && module.globals.iter().filter(|g| &g.name == symbol).count() == 1)
}

/// The view of `module`'s globals: a global's pointer word initialized with
/// another global's address (`SymbolAddr` at `ptr`, a relocation the lane
/// emits) is retyped `*const u8`, at which the interpreter resolves it to
/// that global's allocation (a struct-typed global gets a copy of its struct
/// with those fields retyped; the byte layout is the same). A global without
/// an initializer whose declared type is smaller than
/// [`EXTERN_GLOBAL_RESERVE`] bytes is retyped to an array of at least that
/// many bytes ([`reserve_element`]), at its natural alignment (or its
/// declared one, if larger).
fn view_globals(view: &mut Module) {
    let byte_pointer = Ty::PtrConst(Box::new(Ty::U8));
    let reserved: Vec<(usize, u64)> = {
        let layout = FsymLayout::new(view);
        view.globals
            .iter()
            .enumerate()
            .filter(|(_, g)| g.initializer.is_none())
            .filter_map(|(index, g)| {
                let size = layout.size(&g.ty).ok()?;
                let align = layout.align(&g.ty).ok()?;
                (size < EXTERN_GLOBAL_RESERVE).then_some((index, align))
            })
            .collect()
    };
    if let Some((element, count)) = reserve_element(view).filter(|_| !reserved.is_empty()) {
        for (index, align) in reserved {
            let global = &mut view.globals[index];
            global.ty = Ty::Array(element, count);
            let declared = global.align.map_or(1, u64::from);
            global.align = u32::try_from(align.max(declared)).ok();
        }
    }
    for index in 0..view.globals.len() {
        let Some(init) = view.globals[index].initializer.clone() else {
            continue;
        };
        match (&view.globals[index].ty, &init) {
            (Ty::Ptr, constant) if global_symbol(view, constant) => {
                view.globals[index].ty = byte_pointer.clone();
            }
            (Ty::Struct(id), Constant::Aggregate(fields)) => {
                let Some(def) = view.structs.iter().find(|s| s.id == *id).cloned() else {
                    continue;
                };
                if def.fields.len() != fields.len() {
                    continue;
                }
                let mut retyped = def.clone();
                let mut changed = false;
                for (field, constant) in retyped.fields.iter_mut().zip(fields) {
                    if field.ty == Ty::Ptr && global_symbol(view, constant) {
                        field.ty = byte_pointer.clone();
                        changed = true;
                    }
                }
                if !changed {
                    continue;
                }
                let next = view
                    .structs
                    .iter()
                    .map(|s| s.id.index())
                    .max()
                    .map_or(0, |m| m + 1);
                retyped.id = trust_ir::StructId::new(next);
                retyped.name = format!("{}.interpretable", def.name);
                view.structs.push(retyped);
                view.globals[index].ty = Ty::Struct(trust_ir::StructId::new(next));
            }
            _ => {}
        }
    }
}

/// The element type and length of the array a declared global is retyped to
/// in the view: a type already in `module`'s table (the mid-end appends a
/// pass's new types to the view at the working module's indices, so the
/// view adds none of its own), a one-byte integer if there is one, else the
/// first type of the table whose size is between 1 and 16 bytes and whose
/// alignment is at most 16, repeated to cover [`EXTERN_GLOBAL_RESERVE`]
/// bytes. `None` when the table has no such type (no global is retyped).
fn reserve_element(module: &Module) -> Option<(TyId, u64)> {
    let layout = FsymLayout::new(module);
    let id = |index: usize| u32::try_from(index).ok().map(TyId::new);
    if let Some(index) = module
        .types
        .iter()
        .position(|t| matches!(t, Ty::U8 | Ty::I8))
    {
        return Some((id(index)?, EXTERN_GLOBAL_RESERVE));
    }
    module.types.iter().enumerate().find_map(|(index, ty)| {
        let size = layout.size(ty).ok()?;
        let align = layout.align(ty).ok()?;
        ((1..=16).contains(&size) && align <= 16)
            .then(|| Some((id(index)?, EXTERN_GLOBAL_RESERVE.div_ceil(size))))
            .flatten()
    })
}

/// The body of the C library's `memmove`, `memcpy` or `memset` for the
/// declaration `func` of `module`, or `None` when `func` is not one (module
/// docs, the interpreter's view).
fn libcall_body(module: &Module, pointer_bits: u32, func: &Function) -> Option<Vec<Block>> {
    if !func.is_declaration() {
        return None;
    }
    let (overlap, fill) = match func.name.as_str() {
        "memmove" => (true, false),
        "memcpy" => (false, false),
        "memset" => (false, true),
        _ => return None,
    };
    let sig = module.func_type(func.ty)?;
    let ([dst_ty, second_ty, count_ty], [ret_ty]) = (sig.params.as_slice(), sig.returns.as_slice())
    else {
        return None;
    };
    let second_ok = if fill {
        int_shape(second_ty, pointer_bits).is_some_and(|(bits, _)| (9..=32).contains(&bits))
    } else {
        pointer_like(second_ty)
    };
    if sig.is_vararg
        || !pointer_like(dst_ty)
        || !pointer_like(ret_ty)
        || !second_ok
        || int_shape(count_ty, pointer_bits) != Some((pointer_bits, false))
    {
        return None;
    }
    let v = ValueId::new;
    let node = |inst: Inst, results: Vec<ValueId>| {
        let mut n = InstrNode::new(inst);
        n.results = results;
        n
    };
    let mut body = vec![node(
        Inst::Cast {
            op: CastOp::Bitcast,
            src_ty: count_ty.clone(),
            dst_ty: Ty::Usize,
            operand: v(2),
        },
        vec![v(3)],
    )];
    if fill {
        body.push(node(
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty: second_ty.clone(),
                dst_ty: Ty::U8,
                operand: v(1),
            },
            vec![v(4)],
        ));
        body.push(node(
            Inst::MemSet {
                dst: v(0),
                byte: v(4),
                bytes: v(3),
            },
            Vec::new(),
        ));
    } else {
        body.push(node(
            Inst::MemCopy {
                dst: v(0),
                src: v(1),
                bytes: v(3),
                overlap,
            },
            Vec::new(),
        ));
    }
    let ret = if dst_ty == ret_ty {
        v(0)
    } else {
        body.push(node(
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: dst_ty.clone(),
                dst_ty: ret_ty.clone(),
                operand: v(0),
            },
            vec![v(5)],
        ));
        v(5)
    };
    body.push(node(Inst::Return { values: vec![ret] }, Vec::new()));
    Some(vec![Block {
        id: BlockId::new(0),
        params: vec![
            (v(0), dst_ty.clone()),
            (v(1), second_ty.clone()),
            (v(2), count_ty.clone()),
        ],
        body,
    }])
}

/// The body of the C library's `memcmp` or `bcmp` for the declaration
/// `func` of `module` (module docs, the interpreter's view), or `None`: it
/// loads and compares every one of the `n` byte pairs (the count's bits read
/// as `usize`), as unsigned chars, and returns the difference of the first
/// pair that differs (`compiler_builtins`' value), or 0. Every pair is
/// compared, so an uninitialised byte among the `n` of either object is
/// undefined behaviour, as C requires both objects to hold `n` bytes.
fn compare_body(module: &Module, pointer_bits: u32, func: &Function) -> Option<Vec<Block>> {
    let ret = super::memcmp::library_compare(module, pointer_bits, func)?;
    let sig = module.func_type(func.ty)?;
    let [a_ty, b_ty, count_ty] = sig.params.as_slice() else {
        return None;
    };
    let v = ValueId::new;
    let node = |inst: Inst, results: Vec<ValueId>| {
        let mut n = InstrNode::new(inst);
        n.results = results;
        n
    };
    let as_ptr = |ty: &Ty, operand: ValueId, result: u32| {
        node(
            if *ty == Ty::Ptr {
                Inst::Copy {
                    ty: Ty::Ptr,
                    operand,
                }
            } else {
                Inst::Cast {
                    op: CastOp::PtrToPtr,
                    src_ty: ty.clone(),
                    dst_ty: Ty::Ptr,
                    operand,
                }
            },
            vec![v(result)],
        )
    };
    let load = |ptr: u32, result: u32| {
        node(
            Inst::Load {
                ty: Ty::U8,
                ptr: v(ptr),
                volatile: false,
                align: Some(1),
            },
            vec![v(result)],
        )
    };
    let gep = |base: u32, result: u32| {
        node(
            Inst::GEP {
                pointee_ty: Ty::U8,
                base: v(base),
                indices: vec![v(6)],
                inbounds: false,
            },
            vec![v(result)],
        )
    };
    let zext = |operand: u32, result: u32| {
        node(
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::U8,
                dst_ty: ret.clone(),
                operand: v(operand),
            },
            vec![v(result)],
        )
    };
    let entry = Block {
        id: BlockId::new(0),
        params: vec![
            (v(0), a_ty.clone()),
            (v(1), b_ty.clone()),
            (v(2), count_ty.clone()),
        ],
        body: vec![
            node(
                Inst::Cast {
                    op: CastOp::Bitcast,
                    src_ty: count_ty.clone(),
                    dst_ty: Ty::Usize,
                    operand: v(2),
                },
                vec![v(3)],
            ),
            node(
                Inst::Const {
                    ty: Ty::Usize,
                    value: Constant::Int(0),
                },
                vec![v(4)],
            ),
            node(
                Inst::Const {
                    ty: ret.clone(),
                    value: Constant::Int(0),
                },
                vec![v(5)],
            ),
            node(
                Inst::Br {
                    target: BlockId::new(1),
                    args: vec![v(4), v(5)],
                },
                Vec::new(),
            ),
        ],
    };
    let header = Block {
        id: BlockId::new(1),
        params: vec![(v(6), Ty::Usize), (v(7), ret.clone())],
        body: vec![
            node(
                Inst::ICmp {
                    op: trust_ir::ICmpOp::Ult,
                    ty: Ty::Usize,
                    lhs: v(6),
                    rhs: v(3),
                },
                vec![v(8)],
            ),
            node(
                Inst::CondBr {
                    cond: v(8),
                    then_target: BlockId::new(2),
                    then_args: Vec::new(),
                    else_target: BlockId::new(3),
                    else_args: Vec::new(),
                },
                Vec::new(),
            ),
        ],
    };
    let step = Block {
        id: BlockId::new(2),
        params: Vec::new(),
        body: vec![
            as_ptr(a_ty, v(0), 9),
            gep(9, 10),
            load(10, 11),
            as_ptr(b_ty, v(1), 12),
            gep(12, 13),
            load(13, 14),
            node(
                Inst::ICmp {
                    op: trust_ir::ICmpOp::Ne,
                    ty: Ty::U8,
                    lhs: v(11),
                    rhs: v(14),
                },
                vec![v(15)],
            ),
            node(
                Inst::ICmp {
                    op: trust_ir::ICmpOp::Eq,
                    ty: ret.clone(),
                    lhs: v(7),
                    rhs: v(5),
                },
                vec![v(16)],
            ),
            node(
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::Bool,
                    lhs: v(15),
                    rhs: v(16),
                },
                vec![v(17)],
            ),
            zext(11, 18),
            zext(14, 19),
            node(
                Inst::BinOp {
                    op: BinOp::Sub,
                    ty: ret.clone(),
                    lhs: v(18),
                    rhs: v(19),
                },
                vec![v(20)],
            ),
            node(
                Inst::Select {
                    ty: ret.clone(),
                    cond: v(17),
                    then_val: v(20),
                    else_val: v(7),
                },
                vec![v(21)],
            ),
            node(
                Inst::Const {
                    ty: Ty::Usize,
                    value: Constant::Int(1),
                },
                vec![v(22)],
            ),
            node(
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::Usize,
                    lhs: v(6),
                    rhs: v(22),
                },
                vec![v(23)],
            ),
            node(
                Inst::Br {
                    target: BlockId::new(1),
                    args: vec![v(23), v(21)],
                },
                Vec::new(),
            ),
        ],
    };
    let exit = Block {
        id: BlockId::new(3),
        params: Vec::new(),
        body: vec![node(Inst::Return { values: vec![v(7)] }, Vec::new())],
    };
    Some(vec![entry, header, step, exit])
}

/// The view of every function of `module`, and of its globals.
pub fn interpretable_module(module: &Module) -> Module {
    module_view(module, false)
}

/// [`interpretable_module`] that also gives a `memcmp` or `bcmp`
/// declaration with the C prototype the C library's comparison (module
/// docs). The comparison-call checker's tests run their negative controls
/// in it; the differential never does (OD-164's merge boundary: no default
/// rewrite or differential credit rests on that name-based body).
#[cfg(test)]
pub(crate) fn interpretable_module_with_c_compare(module: &Module) -> Module {
    module_view(module, true)
}

fn module_view(module: &Module, c_compare: bool) -> Module {
    let mut view = module.clone();
    view_globals(&mut view);
    let pointer_bits = FsymLayout::new(module).pointer_bits();
    for (index, func) in module.functions.iter().enumerate() {
        let compare = || {
            c_compare
                .then(|| compare_body(module, pointer_bits, func))
                .flatten()
        };
        if let Some(blocks) = libcall_body(module, pointer_bits, func).or_else(compare) {
            let defined = &mut view.functions[index];
            defined.entry = BlockId::new(0);
            defined.blocks = blocks;
        }
    }
    for (index, func) in module.functions.iter().enumerate() {
        if let Some(viewed) = interpretable(module, func) {
            view.functions[index] = viewed;
        }
    }
    view
}
