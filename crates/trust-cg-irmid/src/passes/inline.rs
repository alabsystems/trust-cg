// trust-cg-irmid/passes/inline.rs - call-site inlining (the OPT-4 port)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Call-site inlining on `trust_ir::Function`: the OPT-4 inliner
//! (`trust-cg-opt/src/ir_inline.rs`, which runs on the native targets' LIR)
//! ported to trust-ir. A direct `call` of a function defined in the module
//! is replaced by a copy of the callee's body whose values and blocks are
//! renamed into fresh ids of the caller. It runs before the memory passes,
//! so a small callee's out-pointer (`sret`) or by-reference parameter, which
//! made the caller's slot escape through the call, becomes plain accesses of
//! the caller's slot that store forwarding and scalar replacement see.
//!
//! **Arrays by address.** The rustc bridge passes a small aggregate as an
//! ARRAY value (`[T x n]`) that is in fact the address of its bytes (an
//! `alloca` of the caller), reads its lanes as `extractfield [T x n] %p, i`,
//! and returns one as the address of the callee's own slot (`ret %slot`);
//! the wasm32 lane and the differential's view read each as the pointee's
//! bytes. A pointer argument for an array parameter is bound to a fresh
//! `load [T x n]` of it at the call, and a pointer returned for an array
//! return to a fresh `load` of it at the `ret`; lane-load scalarization
//! (after this pass) reads those loads lane by lane. Policy: a callee's
//! array-value lane reads are spliced only of a parameter every use of
//! which is such a read (and its write-through `insertfield`s of those
//! lanes, which field-access lowering after the splice spells as stores),
//! a result returned by address only when every use of the call's result
//! is such a lane read, and only arrays of scalars. A callee whose only
//! slots are RETURN SLOTS (returned by address, otherwise only the address
//! of plain loads and stores) may be spliced into a block on a cycle of the
//! caller: no pointer to such a slot outlives the iteration.
//!
//! **The splice** (OPT-4's two tiers): a one-block callee ending in `ret` is
//! spliced in place, its instructions replacing the call and a `copy` of
//! each returned value defining each result. Any other callee splits the
//! call's block: the instructions before the call and `br` to the entry's
//! copy keep the block; the callee's blocks follow, renamed, the entry's
//! copy without parameters (they are bound to the arguments, which dominate
//! the call; an argument that is a thin pointer of another pointer type
//! than its parameter's, as the rustc bridge passes an `alloca` to a
//! closure's `&mut ()`, is bound through a `ptrtoptr` at the call site); each
//! `ret` becomes the result copies and `br` to a fresh
//! continuation block holding the instructions after the call, or, when the
//! callee returns from several blocks, `br` to it passing the returned
//! values, which become the continuation's parameters. The witness names
//! every site, its parameter binding and its renaming; the checker
//! (`trust_ir_mid_tv_inline.rs`) re-derives every side condition, rebuilds
//! the target, and checks its CFG, single definitions and opcode
//! conservation as OPT-4's self-checks do.
//!
//! **Which callees** (each checked again by the checker unless marked as
//! policy): defined in the module with a linkage no other definition can
//! replace at link time (`external`, `internal`, `private`: never `weak`,
//! `linkonce`, their ODR forms, `extern_weak` or `available_externally`), not
//! the caller, not recursive (it reaches no cycle of direct calls through
//! itself), not variadic, naked or feature-stating, no parameter passed by
//! copy, no proof annotation, proof context, summary, source provenance or
//! body gate and no module obligation naming it (so no obligation is ever
//! merged into the caller), a body of allowlisted instructions whose entry
//! no edge targets and that returns, and, for a callee with an `alloca`
//! (the stack bound): no `alloca` lies on a cycle of the callee, the call's
//! block lies on no cycle of the caller (unless every `alloca` is a return
//! slot), the caller lies on no cycle of
//! direct calls, and the slots spliced into one caller total at most
//! [`MAX_SPLICED_SLOT_BYTES`] bytes. A spliced slot is part of the caller's
//! frame for its whole activation, so without the bound a loop (the
//! callee's or the caller's) would allocate it per iteration and a recursion
//! per level, also on paths that never made the call. With it, each spliced
//! `alloca` runs at most once per activation of the caller. Policy only: not in the bridge's
//! never-inline side table ([`crate::MidConfig::never_inline`]:
//! `#[inline(never)]` and `#[cold]` items), not `#[cold]`, and no
//! `extractfield`/`insertfield` through a pointer (the bridge's field access
//! form, which trust-ir's validator reports: a copy would add a finding the
//! wasm32 lane's re-validation of the output refuses).
//!
//! **The wasm size budget** (policy). Sizes count trust-ir instructions,
//! terminators included, after the scalar cleanup the pipeline ran first:
//!
//! * a callee of at most [`TINY_INSTS`] instructions and no `alloca` is
//!   inlined at every call: its body is about the size of the call sequence
//!   it replaces (a slot would also give a frameless caller a frame, with its
//!   prologue and epilogue, and an address-taken callee keeps its own copy);
//! * a callee with exactly one direct call in the module, whose address is
//!   never taken, that is not exported from the linked module (hidden
//!   visibility or a module-local linkage) and not retained, is inlined up to
//!   [`SINGLE_SITE_INSTS`] instructions and [`SINGLE_SITE_BLOCKS`] blocks:
//!   once its one call is gone nothing in this module references it, and
//!   `wasm-ld`'s section garbage collection drops the out-of-line copy, so
//!   the linked module does not grow when no other object of the crate calls
//!   it either (another object's call keeps that copy alive);
//! * any other callee of at most [`SMALL_INSTS`] instructions and
//!   [`MAX_CALLEE_BLOCKS`] blocks (OPT-4's multi-block budget) whose address
//!   is never taken (an address-taken callee stays in the module, so every
//!   copy of it is growth) is inlined
//!   while the caller's growth from such inlines stays within its own size
//!   (at least [`CALLER_GROWTH_FLOOR`]);
//! * a callee with a loop is inlined only at a single call site: its time is
//!   the loop's, which a copy does not shorten, while each copy adds the
//!   loop's code;
//! * the module's growth from tiny and budgeted inlines stays within
//!   [`MODULE_GROWTH_PERCENT`] percent of its instructions (at least
//!   [`MODULE_GROWTH_FLOOR`]), and no caller grows past
//!   [`MAX_FUNCTION_INSTS`] instructions (OPT-4's ceiling) or
//!   [`MAX_FUNCTION_BLOCKS`] blocks.
//!
//! A current typed return slot is loaded at its exact array type immediately
//! before `ret`. In a caller cycle it qualifies only when every consumer
//! reads a fixed scalar lane, so the returned aggregate cannot escape the
//! iteration. The ordinary address, recursion and byte-budget guards apply.
//!
//! The pass visits callers callee-first (the manager's order for it), so a
//! callee is spliced with its own inlines already in its body; an inlined
//! body's calls are not inlined again in the same caller.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeSet, HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{InlineSite, InlineWitness, PassWitness};
use trust_ir::{
    Block, BlockId, CastOp, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage, Module,
    PassMode, Ty, ValueId, Visibility,
};

use super::{MidPass, PassContext, value_types};

/// A callee at most this many instructions is inlined at every call.
pub(crate) const TINY_INSTS: usize = 12;
/// The largest callee inlined under the caller's and the module's budget.
pub(crate) const SMALL_INSTS: usize = 40;
/// The most blocks of a budgeted callee.
pub(crate) const MAX_CALLEE_BLOCKS: usize = 32;
/// The largest single-call-site callee.
pub(crate) const SINGLE_SITE_INSTS: usize = 400;
/// The most blocks of a single-call-site callee.
pub(crate) const SINGLE_SITE_BLOCKS: usize = 128;
/// The least growth a caller may take from budgeted inlines.
pub(crate) const CALLER_GROWTH_FLOOR: usize = 256;
/// No caller grows past this many instructions.
pub(crate) const MAX_FUNCTION_INSTS: usize = 20_000;
/// No caller grows past this many blocks.
pub(crate) const MAX_FUNCTION_BLOCKS: usize = 1024;
/// The module's growth from tiny and budgeted inlines, in percent of its
/// instructions.
pub(crate) const MODULE_GROWTH_PERCENT: usize = 25;
/// The least growth the module may take.
pub(crate) const MODULE_GROWTH_FLOOR: usize = 256;
/// The most bytes of callee `alloca` slots spliced into one caller (the
/// checker's `MAX_SPLICED_SLOT_BYTES`; LLVM's inliner bounds a recursive
/// caller's the same way). Rust code the bridge cannot see may call back
/// into the caller (a vtable, another crate), so every caller is bounded.
pub(crate) const MAX_SPLICED_SLOT_BYTES: u64 = 1024;

/// The module-wide facts the policy reads, derived once per run of the pass
/// from the module it first sees. Inlining copies calls only along existing
/// call chains, so it creates no new cycle, and the counts are a policy
/// estimate.
struct Facts {
    /// Functions on a cycle of direct calls.
    recursive: HashSet<FuncId>,
    /// Functions whose address a constant takes (`fn` constants, closures,
    /// symbol addresses).
    address_taken: HashSet<FuncId>,
    /// Direct call sites (any direct-call form) per callee.
    sites: HashMap<FuncId, usize>,
    /// Functions a module obligation names, and whether one protects every
    /// function.
    obligated: HashSet<FuncId>,
    protect_all: bool,
}

/// The inliner. Holds the `#[inline(never)]` side table and, for one module,
/// the facts and the module's remaining growth budget.
pub(crate) struct Inline {
    never_inline: BTreeSet<String>,
    facts: RefCell<Option<Facts>>,
    module_budget: Cell<Option<usize>>,
}

impl Inline {
    pub(crate) fn new(never_inline: BTreeSet<String>) -> Self {
        Self {
            never_inline,
            facts: RefCell::new(None),
            module_budget: Cell::new(None),
        }
    }
}

/// Instructions of `func`, terminators included.
fn size(func: &Function) -> usize {
    func.blocks.iter().map(|b| b.body.len()).sum()
}

/// The callee a direct-call form names.
fn direct_callee(inst: &Inst) -> Option<FuncId> {
    match inst {
        Inst::Call { callee, .. }
        | Inst::CallCannotUnwind { callee, .. }
        | Inst::Invoke { callee, .. } => Some(*callee),
        _ => None,
    }
}

/// Every function a constant refers to (`fn` constants, closures, symbol
/// addresses by name).
fn constant_functions(
    constant: &Constant,
    by_name: &HashMap<&str, FuncId>,
    out: &mut HashSet<FuncId>,
) {
    let mut pending = vec![constant];
    while let Some(c) = pending.pop() {
        match c {
            Constant::FnDef(id) => {
                out.insert(*id);
            }
            Constant::SymbolAddr { symbol, .. } => {
                if let Some(id) = by_name.get(symbol.as_str()) {
                    out.insert(*id);
                }
            }
            Constant::Closure { func, captures, .. } => {
                out.insert(*func);
                pending.extend(captures.iter());
            }
            Constant::Aggregate(items)
            | Constant::Array(items)
            | Constant::Vector(items)
            | Constant::Sequence(items)
            | Constant::Set(items) => pending.extend(items.iter()),
            Constant::Record(fields) => pending.extend(fields.iter().map(|(_, c)| c)),
            Constant::Splat { elem, .. } => pending.push(elem.as_ref()),
            _ => {}
        }
    }
}

impl Facts {
    fn derive(module: &Module) -> Self {
        let index: HashMap<FuncId, usize> = module
            .functions
            .iter()
            .enumerate()
            .map(|(i, f)| (f.id, i))
            .collect();
        let by_name: HashMap<&str, FuncId> = module
            .functions
            .iter()
            .map(|f| (f.name.as_str(), f.id))
            .collect();
        let mut sites: HashMap<FuncId, usize> = HashMap::new();
        let mut address_taken = HashSet::new();
        let mut calls: Vec<Vec<usize>> = vec![Vec::new(); module.functions.len()];
        for (fi, func) in module.functions.iter().enumerate() {
            for node in func.blocks.iter().flat_map(|b| &b.body) {
                if let Some(callee) = direct_callee(&node.inst) {
                    *sites.entry(callee).or_default() += 1;
                    if let Some(&ci) = index.get(&callee) {
                        calls[fi].push(ci);
                    }
                }
                match &node.inst {
                    Inst::Const { value, .. } => {
                        constant_functions(value, &by_name, &mut address_taken);
                    }
                    Inst::Switch { cases, .. } => {
                        for case in cases {
                            constant_functions(&case.value, &by_name, &mut address_taken);
                        }
                    }
                    Inst::SeqMap { fwd, .. } => {
                        address_taken.insert(*fwd);
                    }
                    _ => {}
                }
            }
        }
        for global in &module.globals {
            if let Some(init) = &global.initializer {
                constant_functions(init, &by_name, &mut address_taken);
            }
        }
        let recursive = recursive_functions(&calls)
            .into_iter()
            .map(|i| module.functions[i].id)
            .collect();
        let mut obligated = HashSet::new();
        let mut protect_all = !module.spec_modules.is_empty();
        for obligation in &module.proof_obligations {
            match (obligation.function, obligation.site.as_ref()) {
                (None, None) => protect_all = true,
                (function, site) => {
                    obligated.extend(function);
                    obligated.extend(site.map(|s| s.function));
                }
            }
        }
        Facts {
            recursive,
            address_taken,
            sites,
            obligated,
            protect_all,
        }
    }
}

/// The functions (by index) on a cycle of `calls`: Tarjan's strongly
/// connected components, iteratively, keeping a component of two or more
/// and a function that calls itself.
fn recursive_functions(calls: &[Vec<usize>]) -> HashSet<usize> {
    let n = calls.len();
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut next = 0usize;
    let mut out = HashSet::new();
    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        // (node, next edge to visit)
        let mut work: Vec<(usize, usize)> = vec![(root, 0)];
        index[root] = next;
        low[root] = next;
        next += 1;
        stack.push(root);
        on_stack[root] = true;
        while let Some(&mut (v, ref mut edge)) = work.last_mut() {
            if let Some(&w) = calls[v].get(*edge) {
                *edge += 1;
                if index[w] == usize::MAX {
                    index[w] = next;
                    low[w] = next;
                    next += 1;
                    stack.push(w);
                    on_stack[w] = true;
                    work.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            work.pop();
            if let Some(&(parent, _)) = work.last() {
                low[parent] = low[parent].min(low[v]);
            }
            if low[v] == index[v] {
                let mut component = Vec::new();
                while let Some(w) = stack.pop() {
                    on_stack[w] = false;
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                if component.len() > 1 || calls[v].contains(&v) {
                    out.extend(component);
                }
            }
        }
    }
    out
}

/// The order the manager visits functions in for this pass: callees before
/// their callers (a postorder of the direct-call graph from each function in
/// index order), restricted to `eligible` (indices into `module.functions`).
pub(crate) fn callee_first_order(module: &Module, eligible: &[usize]) -> Vec<usize> {
    let index: HashMap<FuncId, usize> = module
        .functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.id, i))
        .collect();
    let calls: Vec<Vec<usize>> = module
        .functions
        .iter()
        .map(|f| {
            f.blocks
                .iter()
                .flat_map(|b| &b.body)
                .filter_map(|n| direct_callee(&n.inst))
                .filter_map(|c| index.get(&c).copied())
                .collect()
        })
        .collect();
    let wanted: HashSet<usize> = eligible.iter().copied().collect();
    let mut seen = vec![false; module.functions.len()];
    let mut order = Vec::new();
    for &root in eligible {
        if seen[root] {
            continue;
        }
        seen[root] = true;
        let mut work: Vec<(usize, usize)> = vec![(root, 0)];
        while let Some(&mut (v, ref mut edge)) = work.last_mut() {
            if let Some(&w) = calls[v].get(*edge) {
                *edge += 1;
                if !seen[w] {
                    seen[w] = true;
                    work.push((w, 0));
                }
                continue;
            }
            work.pop();
            if wanted.contains(&v) {
                order.push(v);
            }
        }
    }
    order
}

/// A callee the splice may use, with what the policy reads.
struct Template<'m> {
    func: &'m Function,
    sig: &'m FuncTy,
    /// The entry block's parameter types (the body's view of the arguments).
    entry_params: Vec<Ty>,
    insts: usize,
    has_alloca: bool,
    /// Whether every `alloca` is a return slot (`return_slots`): a splice
    /// into a block on a cycle of the caller keeps it then.
    slots_return_only: bool,
    /// The bytes of its `alloca` slots (`None` when a slot's layout is
    /// unknown, which the stack bound refuses).
    slot_bytes: Option<u64>,
    /// Blocks ending in `ret`.
    returns: usize,
    /// The return positions some `ret` returns by address (an array return
    /// type, a thin pointer value).
    addr_returns: Vec<usize>,
    /// Typed array snapshots loaded from a return slot; on a caller cycle
    /// their users must consume fixed scalar lanes before reuse.
    snapshot_returns: Vec<usize>,
    /// The callee's typing (`typed`).
    types: HashMap<ValueId, Ty>,
    /// Whether the policy may splice it at a single call site.
    single_site: bool,
}

/// A thin pointer type: one address word, no metadata.
fn thin_pointer(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

/// Whether an argument of type `arg` binds a parameter of type `param`:
/// the same type, thin pointers of two pointer types (bound through a
/// `ptrtoptr`, the address the wasm32 lane passes), or a thin pointer where
/// the parameter is an array (bound through a `load` of the array: the
/// rustc bridge passes a small aggregate by the address of its bytes).
fn binds(arg: Option<&Ty>, param: &Ty) -> bool {
    arg.is_some_and(|a| {
        a == param || (thin_pointer(a) && (thin_pointer(param) || by_address(param)))
    })
}

/// Whether `ty` is an array type, which the rustc bridge passes and returns
/// by the address of its bytes.
fn by_address(ty: &Ty) -> bool {
    matches!(ty, Ty::Array(..))
}

/// A current typed array return may load its own matching allocation
/// immediately before returning. Its value has no other use, and the
/// allocation address remains subject to the ordinary no-escape checks.
fn loaded_return_slot(func: &Function, value: ValueId, ty: &Ty) -> Option<ValueId> {
    if !matches!(ty, Ty::Array(..)) {
        return None;
    }
    let mut slot = None;
    for block in &func.blocks {
        for (at, node) in block.body.iter().enumerate() {
            if node.results.as_slice() != [value] {
                continue;
            }
            let Inst::Load {
                ty: loaded,
                ptr,
                volatile: false,
                ..
            } = &node.inst
            else {
                return None;
            };
            if loaded != ty
                || !matches!(block.body.get(at + 1).map(|n| &n.inst), Some(Inst::Return { values }) if values.contains(&value))
            {
                return None;
            }
            let allocation = func
                .blocks
                .iter()
                .flat_map(|b| &b.body)
                .find(|n| n.results.as_slice() == [*ptr])?;
            if !matches!(&allocation.inst, Inst::Alloca { ty: allocated, count: None, .. } if allocated == ty)
            {
                return None;
            }
            slot = Some(*ptr);
        }
    }
    if func.blocks.iter().flat_map(|b| &b.body).any(|n| {
        let mut used = false;
        n.inst.visit_value_operands(|v| used |= v == value);
        used && !matches!(n.inst, Inst::Return { .. })
    }) {
        return None;
    }
    slot
}

/// Whether every `alloca` of `func` is a RETURN SLOT: some `ret` returns it
/// by address (an array return type), and its address is otherwise used
/// only as the address of plain loads and stores (directly or through a
/// `gep` of constant indices used only so). Once spliced, such a slot's
/// address reaches nothing but those accesses and the `load` binding the
/// result, so no pointer to it outlives the iteration of a caller's loop
/// that made it (the wasm32 lane then keeps one frame slot for it).
fn return_slots(func: &Function, sig: &FuncTy, types: &HashMap<ValueId, Ty>) -> bool {
    let slots: HashSet<ValueId> = func
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| matches!(n.inst, Inst::Alloca { .. }))
        .flat_map(|n| n.results.iter().copied())
        .collect();
    let constant = |v: &ValueId| {
        func.blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| n.results == [*v] && matches!(n.inst, Inst::Const { .. }))
    };
    // The constant-index `gep`s of a slot, which are then held to the same
    // rule as the slot (one level).
    let mut derived: HashSet<ValueId> = HashSet::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let (Inst::GEP { base, indices, .. }, [result]) = (&node.inst, node.results.as_slice())
            && slots.contains(base)
            && indices.iter().all(|i| !slots.contains(i) && constant(i))
        {
            derived.insert(*result);
        }
    }
    let watched = |v: &ValueId| slots.contains(v) || derived.contains(v);
    let mut returned: HashSet<ValueId> = HashSet::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let Inst::Return { values } = &node.inst {
            returned.extend(values.iter().filter(|v| slots.contains(v)).copied());
            returned.extend(
                values
                    .iter()
                    .zip(&sig.returns)
                    .filter_map(|(v, t)| loaded_return_slot(func, *v, t)),
            );
        }
    }
    slots.iter().all(|v| returned.contains(v))
        && func
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .all(|node| match &node.inst {
                Inst::Load { .. } => true,
                Inst::Store { value, .. } => !watched(value),
                Inst::GEP { base, indices, .. } => {
                    indices.iter().all(|i| !watched(i))
                        && (!watched(base) || node.results.iter().all(|r| derived.contains(r)))
                }
                Inst::Return { values } => values.iter().zip(&sig.returns).all(|(v, t)| {
                    !watched(v) || (slots.contains(v) && types.get(v) != Some(t) && by_address(t))
                }),
                Inst::Alloca { .. } => true,
                other => {
                    let mut clean = true;
                    other.visit_value_operands(|v| clean &= !watched(&v));
                    clean
                }
            })
}

/// Whether `ty` is an array of scalars (integers, floats, `bool`, `char`,
/// thin pointers): the lanes lane-load scalarization reads one by one.
fn scalar_lanes(module: &Module, ty: &Ty) -> bool {
    let Ty::Array(elem, _) = ty else {
        return false;
    };
    module.ty(*elem).is_some_and(|e| {
        e.is_integer() || e.is_float() || matches!(e, Ty::Bool | Ty::Char) || thin_pointer(e)
    })
}

/// Whether `inst` reads a fixed scalar lane of an array VALUE, either as a
/// typed `extractelement` with a constant usize index or in the bridge's
/// declared-aggregate spelling (`extractfield [T x n] %v, i` with `%v` of
/// that very type): the read of the aggregate's lane, which lane-load
/// scalarization turns into a scalar load once the value is the `load` a
/// splice binds (policy: trust-ir's validator reports the form, so only a
/// value the splice binds that way may be read so in a spliced body).
fn array_lane_read(
    module: &Module,
    func: &Function,
    inst: &Inst,
    types: &HashMap<ValueId, Ty>,
) -> Option<ValueId> {
    match inst {
        Inst::ExtractField {
            ty,
            aggregate,
            field,
        } if by_address(ty)
            && types.get(aggregate) == Some(ty)
            && matches!(ty, Ty::Array(_, n) if u64::from(*field) < *n) =>
        {
            Some(*aggregate)
        }
        Inst::ExtractElement { ty, array, index } => {
            let Ty::Array(elem, length) = types.get(array)? else {
                return None;
            };
            if module.ty(*elem) != Some(ty) {
                return None;
            }
            let n = func
                .blocks
                .iter()
                .flat_map(|b| &b.body)
                .find(|n| n.results.as_slice() == [*index])?;
            match n.inst {
                Inst::Const {
                    ty: Ty::Usize,
                    value: Constant::Int(i),
                } if i >= 0 && u64::try_from(i).is_ok_and(|i| i < *length) => Some(*array),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The splice allowlist (the pass's own copy of the checker's).
fn spliceable(inst: &Inst) -> bool {
    match inst {
        Inst::Alloca { count, .. } => count.is_none(),
        Inst::BinOp { .. }
        | Inst::UnOp { .. }
        | Inst::Overflow { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Cast { .. }
        | Inst::Load { .. }
        | Inst::Store { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::AtomicLoad { .. }
        | Inst::AtomicStore { .. }
        | Inst::AtomicRMW { .. }
        | Inst::CmpXchg { .. }
        | Inst::Fence { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::Return { .. }
        | Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. }
        | Inst::Const { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Undef { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::Unreachable
        | Inst::Copy { .. }
        | Inst::Select { .. }
        | Inst::MemCopy { .. }
        | Inst::MemSet { .. }
        | Inst::MakeAggregate { .. }
        | Inst::ArraySplat { .. } => true,
        _ => false,
    }
}

/// The pass's typing: [`value_types`] plus a direct call's results, typed by
/// its callee's declared returns.
fn typed(module: &Module, func: &Function) -> HashMap<ValueId, Ty> {
    let mut types = value_types(func);
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let Inst::Call { callee, .. } = &node.inst
            && let Some(sig) = module
                .function_by_id(*callee)
                .and_then(|f| module.func_type(f.ty))
            && sig.returns.len() == node.results.len()
        {
            for (value, ty) in node.results.iter().zip(&sig.returns) {
                types.insert(*value, ty.clone());
            }
        }
    }
    types
}

/// Whether `inst` is an `extractfield`/`insertfield` whose operand is not a
/// value of an aggregate type: the rustc bridge's read and write through a
/// pointer to the aggregate. trust-ir's validator reports each such access
/// (`FieldAccessInvalid`), and the wasm32 lane emits a mid-end output only
/// when it reports no finding kind more often than on the input, so a body
/// carrying one is not copied into a caller (policy: the splice itself is
/// exact).
fn field_access_through_pointer(inst: &Inst, types: &HashMap<ValueId, Ty>) -> bool {
    let aggregate = match inst {
        Inst::ExtractField { aggregate, .. } | Inst::InsertField { aggregate, .. } => aggregate,
        _ => return false,
    };
    !matches!(
        types.get(aggregate),
        Some(Ty::Struct(_) | Ty::Record(_) | Ty::Tuple(_) | Ty::Enum(_) | Ty::Closure(_))
    )
}

impl Template<'_> {
    /// The positions a `ret` of `values` returns by address: a thin pointer
    /// where the declared return is an array.
    fn addressed(&self, values: &[ValueId]) -> Vec<usize> {
        values
            .iter()
            .zip(&self.sig.returns)
            .enumerate()
            .filter(|(_, (v, t))| self.types.get(v) != Some(t) && by_address(t))
            .map(|(k, _)| k)
            .collect()
    }
}

impl Inline {
    /// The callee `id` as a template for a call from `caller`, or `None`.
    fn template<'m>(
        &self,
        module: &'m Module,
        facts: &Facts,
        caller: FuncId,
        id: FuncId,
    ) -> Option<Template<'m>> {
        if id == caller || facts.recursive.contains(&id) {
            return None;
        }
        let func = module.function_by_id(id)?;
        if func.is_declaration()
            || !matches!(
                func.linkage,
                Linkage::External | Linkage::Internal | Linkage::Private
            )
            || self.never_inline.contains(&func.name)
            || func.attrs.cold
            || func.attrs.naked
            || !func.attrs.target_features.is_empty()
            || func
                .attrs
                .params
                .iter()
                .any(|p| p.byval || matches!(p.pass, Some(PassMode::Indirect { .. })))
        {
            return None;
        }
        if facts.protect_all
            || facts.obligated.contains(&id)
            || !func.proofs.is_empty()
            || func.summary.is_some()
            || func.source_provenance.is_some()
            || func.body_gate.is_some()
        {
            return None;
        }
        let sig = module.func_type(func.ty)?;
        if sig.is_vararg {
            return None;
        }
        let entry = func.blocks.iter().find(|b| b.id == func.entry)?;
        if entry.params.len() != sig.params.len()
            || entry
                .params
                .iter()
                .zip(&sig.params)
                .any(|((_, t), p)| t != p && !(thin_pointer(t) && thin_pointer(p)))
        {
            return None;
        }
        let types = typed(module, func);
        let ids: HashSet<BlockId> = func.blocks.iter().map(|b| b.id).collect();
        if ids.len() != func.blocks.len() {
            return None;
        }
        // The array parameters every use of which is a lane read: a splice
        // binds them to a `load` (from a pointer argument) that lane-load
        // scalarization takes apart (policy).
        let mut lane_params: HashSet<ValueId> = entry
            .params
            .iter()
            .filter(|(_, ty)| scalar_lanes(module, ty))
            .map(|(v, _)| *v)
            .collect();
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            let read = array_lane_read(module, func, &node.inst, &types);
            node.inst.visit_value_operands(|v| {
                if read != Some(v) {
                    lane_params.remove(&v);
                }
            });
        }
        // The results of those reads: once the splice binds their parameter
        // and lane-load scalarization runs, each is a scalar of its lane's
        // type, which field-access lowering (after it) stores through a
        // pointer.
        let lane_values: HashSet<ValueId> = func
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .filter(|n| {
                array_lane_read(module, func, &n.inst, &types)
                    .is_some_and(|v| lane_params.contains(&v))
            })
            .flat_map(|n| n.results.iter().copied())
            .collect();
        let spliced_lane = |inst: &Inst| match inst {
            Inst::ExtractField { .. } => array_lane_read(module, func, inst, &types)
                .is_some_and(|v| lane_params.contains(&v)),
            Inst::InsertField { value, .. } => lane_values.contains(value),
            _ => false,
        };
        let mut returns = 0usize;
        let mut addr_returns: Vec<usize> = Vec::new();
        let mut snapshot_returns: Vec<usize> = Vec::new();
        let mut has_alloca = false;
        let mut slot_bytes = Some(0u64);
        let mut alloca_blocks: HashSet<BlockId> = HashSet::new();
        for block in &func.blocks {
            let (last, body) = block.body.split_last()?;
            if !matches!(
                last.inst,
                Inst::Br { .. }
                    | Inst::CondBr { .. }
                    | Inst::Switch { .. }
                    | Inst::Return { .. }
                    | Inst::Unreachable
            ) || body.iter().any(|n| n.inst.is_terminator())
            {
                return None;
            }
            for node in &block.body {
                if !spliceable(&node.inst)
                    || !node.proofs.is_empty()
                    || node.proof_context.is_some()
                    || (field_access_through_pointer(&node.inst, &types)
                        && !spliced_lane(&node.inst))
                {
                    return None;
                }
                if let Inst::Alloca { ty, .. } = &node.inst {
                    has_alloca = true;
                    alloca_blocks.insert(block.id);
                    let bytes = module
                        .ty_layout_shape(ty)
                        .ok()
                        .and_then(|shape| shape.size_bytes());
                    slot_bytes = slot_bytes.zip(bytes).and_then(|(a, b)| a.checked_add(b));
                }
            }
            for edge in last.inst.successor_edges() {
                if edge.target == func.entry || !ids.contains(&edge.target) {
                    return None;
                }
            }
            if let Inst::Return { values } = &last.inst {
                returns += 1;
                if values.len() != sig.returns.len()
                    || values.iter().zip(&sig.returns).any(|(v, t)| {
                        types.get(v) != Some(t)
                            && !(types.get(v).is_some_and(thin_pointer) && by_address(t))
                    })
                {
                    return None;
                }
                for (k, (v, t)) in values.iter().zip(&sig.returns).enumerate() {
                    if types.get(v) != Some(t) && !addr_returns.contains(&k) {
                        addr_returns.push(k);
                    }
                    if loaded_return_slot(func, *v, t).is_some() && !snapshot_returns.contains(&k) {
                        snapshot_returns.push(k);
                    }
                }
            }
        }
        if returns == 0 {
            return None;
        }
        let insts = size(func);
        let exported = func.visibility == Visibility::Default
            && !matches!(func.linkage, Linkage::Internal | Linkage::Private);
        let single_site = !exported
            && !func.retained
            && !facts.address_taken.contains(&id)
            && facts.sites.get(&id).copied() == Some(1)
            && insts <= SINGLE_SITE_INSTS
            && func.blocks.len() <= SINGLE_SITE_BLOCKS;
        // A callee with a loop is copied only to its single call site: its
        // time is the loop's, which the copy does not shorten, while every
        // copy adds the loop's code.
        // A callee whose address is taken stays in the module whatever its
        // call sites, so each copy of it is growth: only a tiny one is copied.
        let cyclic = cyclic_blocks(func);
        // The stack bound (module docs): a slot the callee makes on one of its
        // own cycles would sit on a cycle of the caller once spliced, carved
        // per iteration and held until the caller returns.
        if alloca_blocks.iter().any(|b| cyclic.contains(b)) {
            return None;
        }
        let looping = !cyclic.is_empty();
        let tiny = insts <= TINY_INSTS && !has_alloca;
        let slots_return_only = has_alloca && return_slots(func, sig, &types);
        let budgeted = insts <= SMALL_INSTS
            && func.blocks.len() <= MAX_CALLEE_BLOCKS
            && !facts.address_taken.contains(&id);
        if !(single_site || (!looping && (tiny || budgeted))) {
            return None;
        }
        Some(Template {
            func,
            sig,
            entry_params: entry.params.iter().map(|(_, t)| t.clone()).collect(),
            insts,
            has_alloca,
            slots_return_only,
            slot_bytes,
            returns,
            addr_returns,
            snapshot_returns,
            types,
            single_site,
        })
    }
}

/// Every value `func` names (parameters, results, operands, debug names).
fn names(func: &Function) -> HashSet<ValueId> {
    let mut all = HashSet::new();
    for block in &func.blocks {
        all.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            all.extend(node.results.iter().copied());
            node.inst.visit_value_operands(|v| {
                all.insert(v);
            });
        }
    }
    if let Some(names) = &func.value_names {
        all.extend(names.iter().map(|(v, _)| *v));
    }
    all
}

/// The blocks of `func` on a cycle.
fn cyclic_blocks(func: &Function) -> HashSet<BlockId> {
    let succ: HashMap<BlockId, Vec<BlockId>> = func
        .blocks
        .iter()
        .map(|b| {
            let targets = b
                .body
                .last()
                .map(|n| n.inst.successor_edges().iter().map(|e| e.target).collect())
                .unwrap_or_default();
            (b.id, targets)
        })
        .collect();
    let mut out = HashSet::new();
    for block in &func.blocks {
        let mut seen = HashSet::new();
        let mut work: Vec<BlockId> = succ.get(&block.id).cloned().unwrap_or_default();
        while let Some(b) = work.pop() {
            if b == block.id {
                out.insert(block.id);
                break;
            }
            if seen.insert(b) {
                work.extend(succ.get(&b).into_iter().flatten().copied());
            }
        }
    }
    out
}

/// `inst` with its `br`/`condbr`/`switch` targets moved through `map`.
fn retarget(inst: &mut Inst, map: &HashMap<BlockId, BlockId>) {
    let mv = |b: &mut BlockId| {
        if let Some(n) = map.get(b) {
            *b = *n;
        }
    };
    match inst {
        Inst::Br { target, .. } => mv(target),
        Inst::CondBr {
            then_target,
            else_target,
            ..
        } => {
            mv(then_target);
            mv(else_target);
        }
        Inst::Switch { default, cases, .. } => {
            mv(default);
            for case in cases {
                mv(&mut case.target);
            }
        }
        _ => {}
    }
}

/// A copy of a callee node in the caller: renamed, retargeted, the callee's
/// span, no lexical scope (an index into the callee's table) and no proof.
fn cloned(
    node: &InstrNode,
    values: &HashMap<ValueId, ValueId>,
    blocks: &HashMap<BlockId, BlockId>,
) -> InstrNode {
    let mut out = node.clone();
    trust_ir::mem2reg::rewrite_node(&mut out, values);
    retarget(&mut out.inst, blocks);
    out.scope = None;
    out.proofs.clear();
    out.proof_context = None;
    out
}

/// A binding node at the call site, with the call's span and scope.
fn at_call(call: &InstrNode, inst: Inst, results: Vec<ValueId>) -> InstrNode {
    InstrNode {
        inst,
        results,
        proofs: Vec::new(),
        span: call.span,
        proof_context: None,
        scope: call.scope,
    }
}

/// The nodes replacing one callee `ret` of `values` (already renamed): the
/// `load` of each array returned by address (`addressed`, its positions),
/// into fresh values recorded in `loaded`, then the binding.
#[allow(clippy::too_many_arguments)]
fn returned(
    call: &InstrNode,
    mut values: Vec<ValueId>,
    addressed: &[usize],
    returns: &[Ty],
    continuation: Option<BlockId>,
    joined: bool,
    fresh: &mut Fresh,
    loaded: &mut Vec<ValueId>,
) -> Vec<InstrNode> {
    let mut out: Vec<InstrNode> = Vec::new();
    for &k in addressed {
        let value = fresh.value();
        out.push(at_call(
            call,
            Inst::Load {
                ty: returns[k].clone(),
                ptr: values[k],
                volatile: false,
                align: Some(1),
            },
            vec![value],
        ));
        loaded.push(value);
        values[k] = value;
    }
    if joined {
        let target = continuation.expect("a joined return has a continuation");
        out.push(at_call(
            call,
            Inst::Br {
                target,
                args: values,
            },
            Vec::new(),
        ));
        return out;
    }
    out.extend(
        values
            .iter()
            .zip(&call.results)
            .zip(returns)
            .map(|((value, result), ty)| {
                at_call(
                    call,
                    Inst::Copy {
                        ty: ty.clone(),
                        operand: *value,
                    },
                    vec![*result],
                )
            }),
    );
    if let Some(target) = continuation {
        out.push(at_call(
            call,
            Inst::Br {
                target,
                args: Vec::new(),
            },
            Vec::new(),
        ));
    }
    out
}

/// Fresh ids for one function.
struct Fresh {
    value: u32,
    block: u32,
}

impl Fresh {
    fn value(&mut self) -> ValueId {
        let v = ValueId::new(self.value);
        self.value += 1;
        v
    }
    fn block(&mut self) -> BlockId {
        let b = BlockId::new(self.block);
        self.block += 1;
        b
    }
}

/// Splice `t` at node `index` of block position `bi` of `cur`; returns the
/// site and the block position and node index to continue scanning from.
fn splice(
    cur: &mut Function,
    bi: usize,
    index: usize,
    t: &Template<'_>,
    caller_types: &HashMap<ValueId, Ty>,
    fresh: &mut Fresh,
) -> (InlineSite, usize, usize) {
    let call = cur.blocks[bi].body[index].clone();
    let Inst::Call { callee, args } = &call.inst else {
        unreachable!("a site is a call");
    };
    let callee_fn = t.func;
    let entry = callee_fn
        .blocks
        .iter()
        .find(|b| b.id == callee_fn.entry)
        .expect("a template has its entry");
    // Each parameter is bound to its argument, to a `ptrtoptr` of a thin
    // pointer argument of another pointer type, or to the `load` of an array
    // passed by its address.
    let mut params: Vec<(ValueId, ValueId)> = Vec::with_capacity(args.len());
    let mut casts: Vec<InstrNode> = Vec::new();
    for ((p, ty), arg) in entry.params.iter().zip(args) {
        match caller_types.get(arg) {
            Some(from) if from != ty => {
                let bound = fresh.value();
                let inst = if by_address(ty) {
                    Inst::Load {
                        ty: ty.clone(),
                        ptr: *arg,
                        volatile: false,
                        align: Some(1),
                    }
                } else {
                    Inst::Cast {
                        op: CastOp::PtrToPtr,
                        src_ty: from.clone(),
                        dst_ty: ty.clone(),
                        operand: *arg,
                    }
                };
                casts.push(at_call(&call, inst, vec![bound]));
                params.push((*p, bound));
            }
            _ => params.push((*p, *arg)),
        }
    }
    let mut values: Vec<(ValueId, ValueId)> = Vec::new();
    for block in &callee_fn.blocks {
        if block.id != callee_fn.entry {
            for (v, _) in &block.params {
                values.push((*v, fresh.value()));
            }
        }
        for node in &block.body {
            for r in &node.results {
                values.push((*r, fresh.value()));
            }
        }
    }
    let mut value_map: HashMap<ValueId, ValueId> = values.iter().copied().collect();
    value_map.extend(params.iter().copied());
    let renamed = |vs: &[ValueId], map: &HashMap<ValueId, ValueId>| -> Vec<ValueId> {
        vs.iter().map(|v| *map.get(v).unwrap_or(v)).collect()
    };
    let in_place = callee_fn.blocks.len() == 1;
    let block_id = cur.blocks[bi].id;
    let mut loaded: Vec<ValueId> = Vec::new();
    if in_place {
        let (last, body) = callee_fn.blocks[0]
            .body
            .split_last()
            .expect("a template block is not empty");
        let Inst::Return { values: rets } = &last.inst else {
            unreachable!("a one-block template returns");
        };
        let empty = HashMap::new();
        let mut nodes: Vec<InstrNode> = casts;
        nodes.extend(body.iter().map(|n| cloned(n, &value_map, &empty)));
        nodes.extend(returned(
            &call,
            renamed(rets, &value_map),
            &t.addressed(rets),
            &t.sig.returns,
            None,
            false,
            fresh,
            &mut loaded,
        ));
        let resume = index + nodes.len();
        cur.blocks[bi].body.splice(index..=index, nodes);
        let site = InlineSite {
            block: block_id,
            index,
            callee: *callee,
            params,
            values,
            blocks: Vec::new(),
            continuation: None,
            returned: loaded,
        };
        return (site, bi, resume);
    }
    let blocks: Vec<(BlockId, BlockId)> = callee_fn
        .blocks
        .iter()
        .map(|b| (b.id, fresh.block()))
        .collect();
    let continuation = fresh.block();
    let block_map: HashMap<BlockId, BlockId> = blocks.iter().copied().collect();
    let joined = t.returns > 1;
    let tail = cur.blocks[bi].body.split_off(index + 1);
    cur.blocks[bi].body.pop();
    cur.blocks[bi].body.extend(casts);
    cur.blocks[bi].body.push(at_call(
        &call,
        Inst::Br {
            target: block_map[&callee_fn.entry],
            args: Vec::new(),
        },
        Vec::new(),
    ));
    let mut new_blocks: Vec<Block> = Vec::with_capacity(callee_fn.blocks.len() + 1);
    for block in &callee_fn.blocks {
        let mut out = Block::new(block_map[&block.id]);
        if block.id != callee_fn.entry {
            out.params = block
                .params
                .iter()
                .map(|(v, ty)| (value_map[v], ty.clone()))
                .collect();
        }
        for node in &block.body {
            if let Inst::Return { values: rets } = &node.inst {
                out.body.extend(returned(
                    &call,
                    renamed(rets, &value_map),
                    &t.addressed(rets),
                    &t.sig.returns,
                    Some(continuation),
                    joined,
                    fresh,
                    &mut loaded,
                ));
            } else {
                out.body.push(cloned(node, &value_map, &block_map));
            }
        }
        new_blocks.push(out);
    }
    let mut cont = Block::new(continuation);
    if joined {
        cont.params = call
            .results
            .iter()
            .copied()
            .zip(t.sig.returns.iter().cloned())
            .collect();
    }
    cont.body = tail;
    let inserted = new_blocks.len();
    new_blocks.push(cont);
    cur.blocks.splice(bi + 1..bi + 1, new_blocks);
    let site = InlineSite {
        block: block_id,
        index,
        callee: *callee,
        params,
        values,
        blocks,
        continuation: Some(continuation),
        returned: loaded,
    };
    (site, bi + 1 + inserted, 0)
}

impl MidPass for Inline {
    fn name(&self) -> &'static str {
        super::INLINE_NAME
    }

    fn callee_first(&self) -> bool {
        true
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let module = cx.module;
        if self.facts.borrow().is_none() {
            *self.facts.borrow_mut() = Some(Facts::derive(module));
            let total: usize = module.functions.iter().map(size).sum();
            self.module_budget.set(Some(
                (total * MODULE_GROWTH_PERCENT / 100).max(MODULE_GROWTH_FLOOR),
            ));
        }
        let facts_ref = self.facts.borrow();
        let facts = facts_ref.as_ref()?;
        // Cheap pre-scan: any call of a template at all?
        let mut templates: HashMap<FuncId, Option<Template<'_>>> = HashMap::new();
        let mut any = false;
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            if let Inst::Call { callee, .. } = &node.inst {
                let t = templates
                    .entry(*callee)
                    .or_insert_with(|| self.template(module, facts, func.id, *callee));
                any |= t.is_some();
            }
        }
        if !any {
            return None;
        }
        let mut cur = func.clone();
        let universe = names(&cur);
        let mut fresh = Fresh {
            value: universe
                .iter()
                .map(|v| v.index())
                .max()
                .map_or(0, |m| m + 1),
            block: cur
                .blocks
                .iter()
                .map(|b| b.id.index())
                .max()
                .map_or(0, |m| m + 1),
        };
        let cyclic = cyclic_blocks(func);
        let caller_types = typed(module, func);
        // Per value of the caller: whether every use reads one lane of it as
        // an array value (`array_lane_read`).
        let mut result_reads: HashMap<ValueId, bool> = HashMap::new();
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            let read = array_lane_read(cx.module, func, &node.inst, &caller_types);
            node.inst.visit_value_operands(|v| {
                let all = result_reads.entry(v).or_insert(true);
                *all &= read == Some(v);
            });
        }
        let start = size(func);
        let caller_budget = start.max(CALLER_GROWTH_FLOOR);
        let mut caller_growth = 0usize;
        let mut slots = 0u64;
        // The stack bound (module docs): no allocating callee into a caller
        // on a cycle of direct calls.
        let recursive_caller = facts.recursive.contains(&func.id);
        let mut total = start;
        let mut sites: Vec<InlineSite> = Vec::new();
        // Block ids whose cyclicity is the original block's they were split
        // from (a continuation inherits its block's).
        let mut origin: HashMap<BlockId, BlockId> = HashMap::new();
        let (mut bi, mut ni) = (0usize, 0usize);
        // Blocks cloned from a callee are not scanned again.
        let mut cloned_blocks: HashSet<BlockId> = HashSet::new();
        while bi < cur.blocks.len() {
            if cloned_blocks.contains(&cur.blocks[bi].id) || ni >= cur.blocks[bi].body.len() {
                bi += 1;
                ni = 0;
                continue;
            }
            let node = &cur.blocks[bi].body[ni];
            let Inst::Call { callee, args } = &node.inst else {
                ni += 1;
                continue;
            };
            let Some(Some(t)) = templates.get(callee) else {
                ni += 1;
                continue;
            };
            let block_id = cur.blocks[bi].id;
            let home = origin.get(&block_id).copied().unwrap_or(block_id);
            let growth = t.insts.saturating_sub(1) + t.sig.returns.len() + 1;
            let budget_left = self.module_budget.get().unwrap_or(0);
            let tiny = t.insts <= TINY_INSTS && !t.has_alloca;
            let slots_after = if t.has_alloca {
                t.slot_bytes
                    .and_then(|b| slots.checked_add(b))
                    .filter(|&b| !recursive_caller && b <= MAX_SPLICED_SLOT_BYTES)
            } else {
                Some(slots)
            };
            // A result returned by address is read only lane by lane, so the
            // `load` the splice binds it to is taken apart (policy).
            let lanes_only = t.addr_returns.iter().all(|&k| {
                node.results.get(k).is_some_and(|&r| {
                    scalar_lanes(module, &t.sig.returns[k])
                        && result_reads.get(&r).copied().unwrap_or(true)
                })
            });
            let snapshot_lanes_only = !cyclic.contains(&home)
                || t.snapshot_returns.iter().all(|&k| {
                    node.results.get(k).is_some_and(|&r| {
                        scalar_lanes(module, &t.sig.returns[k])
                            && result_reads.get(&r).copied().unwrap_or(true)
                    })
                });
            let fits = lanes_only
                && snapshot_lanes_only
                && node.results.len() == t.sig.returns.len()
                && args.len() == t.sig.params.len()
                && args
                    .iter()
                    .zip(&t.entry_params)
                    .all(|(a, ty)| binds(caller_types.get(a), ty))
                && node.proofs.is_empty()
                && node.proof_context.is_none()
                && !(t.has_alloca && !t.slots_return_only && cyclic.contains(&home))
                && slots_after.is_some()
                && total + growth <= MAX_FUNCTION_INSTS
                && cur.blocks.len() + t.func.blocks.len() < MAX_FUNCTION_BLOCKS
                && (t.single_site
                    || (tiny && growth <= budget_left)
                    || (growth <= budget_left && caller_growth + growth <= caller_budget));
            if !fits {
                ni += 1;
                continue;
            }
            if !t.single_site {
                self.module_budget.set(Some(budget_left - growth));
                if !tiny {
                    caller_growth += growth;
                }
            }
            total += growth;
            slots = slots_after.unwrap_or(slots);
            let in_place = t.func.blocks.len() == 1;
            let before = cur.blocks.len();
            let (site, next_bi, next_ni) = splice(&mut cur, bi, ni, t, &caller_types, &mut fresh);
            if !in_place {
                for b in &cur.blocks[bi + 1..bi + 1 + (cur.blocks.len() - before - 1)] {
                    cloned_blocks.insert(b.id);
                }
                if let Some(cont) = site.continuation {
                    origin.insert(cont, home);
                }
            }
            sites.push(site);
            bi = next_bi;
            ni = next_ni;
        }
        if sites.is_empty() {
            return None;
        }
        Some((cur, PassWitness::Inline(InlineWitness { sites })))
    }
}
