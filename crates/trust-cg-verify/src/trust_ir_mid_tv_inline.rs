// trust-cg-verify/trust_ir_mid_tv_inline.rs - the inliner's checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of call-site inlining ([`InlineWitness`]): a direct `call` of
//! a function defined in the module is replaced by a renamed copy of the
//! callee's body. The checks are the OPT-4 inliner's
//! (`trust-cg-opt/src/ir_inline.rs`: fresh renaming, the multi-block splice,
//! `verify_opcode_conservation`, the CFG well-formedness check, interposable
//! exclusion), re-derived here for `trust_ir::Function`, plus an exact rebuild.
//!
//! What is re-derived from the SOURCE and the module alone, per site, on the
//! function the earlier sites of the witness produced:
//!
//! * **The callee's body is the one the call reaches.** The site is a plain
//!   `call` (not `invoke`, not an indirect or no-unwind call) of a function
//!   other than the caller, defined in the module with a linkage no other
//!   definition can replace at link time (`external`, `internal`, `private`;
//!   `weak`, `linkonce`, their ODR forms, `extern_weak` and
//!   `available_externally` are refused), not variadic, not naked, stating no
//!   target features, and with no parameter passed by copy (`byval` or an
//!   indirect pass mode, where the callee receives its own copy and the call
//!   is not a plain binding).
//! * **No proof obligation is merged.** The callee carries no proof
//!   annotation, call-site proof context, summary, source provenance or body
//!   gate, and no module obligation names it or one of its sites (nor is there
//!   an unscoped obligation or a spec module): every obligation of the module
//!   is preserved byte for byte, none moves into the caller.
//! * **The callee is not recursive**: it does not reach itself through the
//!   module's direct calls (inlining one level of a recursive function would
//!   be correct, but the inliner never does it and the checker holds it to
//!   that).
//! * **The callee's body can be spliced.** Its entry parameters have the
//!   declared parameter types (thin pointers may be of other pointer types,
//!   as the rustc bridge declares a closure's `&()` environment `&mut ()` in
//!   its body); its entry block is the target of no edge (so its parameters are bound exactly once, to the arguments);
//!   every block ends in exactly one `br`, `condbr`, `switch`, `ret` or
//!   `unreachable`; at least one block returns, each `ret` with the declared
//!   number of values, each of the declared return type (or a thin pointer
//!   where that type is an array, below); every instruction is
//!   on this module's allowlist (arithmetic, comparisons, casts, plain and
//!   atomic memory accesses, count-free `alloca`, address computations,
//!   aggregates, constants, `assume`/`assert`, copies, selects, bulk memory
//!   operations, direct and indirect calls); exception handling, coroutines,
//!   ownership, binding-frame and dialect instructions are refused.
//! * **The stack bound.** A spliced `alloca` is a slot of the caller's frame
//!   for its whole activation, while the source makes it once per call and
//!   frees it on return. So a callee with an `alloca` is not spliced when one
//!   of its `alloca`s lies on a cycle of the callee, nor into a block on a
//!   cycle of the caller (either way the target would allocate it per
//!   iteration) unless every `alloca` of the callee is a RETURN SLOT (a
//!   `ret` returns it by address, and its address, and that of each `gep`
//!   of it by constant indices, is otherwise used only as the address of
//!   plain loads and stores: once spliced it reaches nothing but
//!   those accesses and the `load` binding the result, so no pointer to it
//!   outlives the iteration that made it, and the wasm32 lane keeps one
//!   frame slot for it, while the reference interpreter allocates it per
//!   iteration as the source allocates it per call), nor into a caller that
//!   reaches itself through direct calls
//!   (per recursion level, also on paths that never make the call), and the
//!   slots spliced into one caller by one witness total at most
//!   [`MAX_SPLICED_SLOT_BYTES`] bytes of known layout (a caller may still
//!   recur through calls the module does not show: an indirect call, another
//!   object). Each spliced `alloca` then runs at most once per activation of
//!   the caller, so this bounds the caller's frame growth; it is a resource
//!   condition the interpreter differential cannot see.
//!   A typed array load immediately before `ret` may identify that same
//!   return slot. It must load a matching allocation, have no other use,
//!   and, for a caller cycle, its call result must be consumed only by fixed
//!   scalar lane reads. The checker re-derives these facts from both bodies.
//! * **Argument and return binding.** The call has one argument per entry
//!   parameter and one result per declared return, and the witness binds the
//!   `i`-th entry parameter to the `i`-th argument when the argument has
//!   exactly the entry parameter's type (this module's typing, a call's result
//!   typed by its callee's declaration). An argument that is a thin pointer
//!   (`ptr`, `&T`, `&mut T`, `*const T`, `*mut T`) of another pointer type
//!   than the entry parameter's is bound through a fresh `ptrtoptr` of it to the
//!   parameter's type, inserted at the call site before the body: the rustc
//!   bridge passes such pointers (an `alloca`'s `ptr` to a closure's `&mut
//!   ()`), which trust-ir's validator reports (`CallArgTypeMismatch`) and the
//!   interpreter refuses to call, while the wasm32 lane passes the address.
//!   An argument that is a thin pointer where the parameter is an ARRAY
//!   (`[T x n]`, the rustc bridge's spelling of a small aggregate passed by
//!   value) is bound through a fresh `load [T x n], ptr <argument>` of
//!   alignment 1 at the call site: the bridge passes the address of the aggregate's
//!   bytes, the wasm32 lane passes such an aggregate by its address, and the
//!   differential's view reads that argument as exactly this load of the
//!   pointee's bytes at the call.
//!   In the target the call's results are defined by
//!   `copy <return type>` of the returned values (one `ret`) or are the
//!   continuation block's parameters, passed by every returning block (more
//!   than one). A returned value that is a thin pointer where the declared
//!   return is an array (the bridge returns the address of a slot holding
//!   the aggregate) is returned through a fresh `load <return type>, ptr
//!   <value>` (align 1) inserted before that block's binding: the pointee's
//!   bytes at the return, as the view and the lane (which copies them out)
//!   read it. The witness names these loads (`returned`) in the callee's
//!   block order.
//! * **Fresh renaming.** Every callee value other than an entry parameter
//!   maps to a distinct caller value defined or used nowhere in the function
//!   so far; every callee block, and the continuation, to a distinct block id
//!   the function does not have.
//!
//! The rebuilt target, per site: a one-block callee whose block ends in `ret`
//! may be spliced in place (no `blocks` in the witness): the binding
//! `ptrtoptr`s and its instructions, renamed, replace the call, then a `copy`
//! per result. Otherwise the call's block is split: the instructions before
//! the call, the binding `ptrtoptr`s and `br` to the entry's copy keep the
//! block (its id, parameters and predecessors); the callee's
//! blocks follow, renamed, the entry's copy without parameters, each `ret`
//! replaced as above by the result copies and `br` to the continuation (or by
//! `br` to it passing the returned values); the continuation follows with
//! the instructions after the call and the old terminator. Cloned
//! instructions keep their span, drop their lexical scope (an index into the
//! callee's scope table), and carry no proof; the binding instructions take
//! the call's span and scope.
//!
//! Independently of the rebuild, the TARGET must be a well-formed CFG (the
//! source's entry block; unique block ids; each block non-empty and ending in
//! its only terminator; every edge to an existing block), define every value
//! once, and conserve opcodes and effects: its multiset of instructions
//! (operands and block targets abstracted) is the source's, minus one `call`
//! per site, plus each callee's instructions except its `ret`s, plus the
//! binding casts, copies and branches. A dropped or duplicated instruction — a
//! store, a call — is refused by name before the exact comparison.
//!
//! Each splice is a REFINEMENT of the reference interpreter's semantics: a
//! direct call of a defined function binds the callee's entry parameters to
//! the arguments, runs its body over values of its own (never the caller's),
//! and binds the results to the returned values; the splice runs the same
//! instructions, in the same order, over fresh caller values, with the
//! parameters substituted by the arguments (which dominate the call) and the
//! results bound at the join. The interpreter does not free an `alloca` when
//! its function returns, so the inlined allocation lives exactly as long as
//! the source's. An array passed or returned by its address is, at the
//! boundary, the load of its bytes the view performs there, and the target
//! performs that load at the same point. What the splice removes is the
//! call boundary's own checks: a poison argument or returned value is
//! undefined behaviour at a call (`check_signature_values`), and an argument
//! of another pointer type is a signature mismatch there; the target runs
//! on in both cases. It also
//! removes one frame of call depth (a resource limit) and changes the debug
//! metadata of the cloned instructions.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use trust_ir::{
    Block, BlockId, CastOp, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage, Module,
    PassMode, Ty, ValueId,
};

use super::{MidTvError, WitnessVerdict, block_positions};

/// The most bytes of callee `alloca` slots one witness splices into one
/// caller (module documentation, the stack bound).
pub const MAX_SPLICED_SLOT_BYTES: u64 = 1024;

/// One inlined call site, in the function the witness's earlier sites
/// produced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InlineSite {
    /// The block holding the `call` and the call's index in it.
    pub block: BlockId,
    pub index: usize,
    pub callee: FuncId,
    /// Each entry parameter of the callee and the value it is bound to, in
    /// parameter order: the call's argument, or, when the argument is a thin
    /// pointer of another pointer type than the parameter's, a fresh value
    /// defined by `ptrtoptr` of it at the call site.
    pub params: Vec<(ValueId, ValueId)>,
    /// Each other callee value (a block parameter or an instruction result)
    /// and the fresh caller value it becomes, in the callee's block order.
    pub values: Vec<(ValueId, ValueId)>,
    /// Each callee block and the fresh caller block it becomes, in the
    /// callee's block order; empty for an in-place splice of a one-block
    /// callee.
    pub blocks: Vec<(BlockId, BlockId)>,
    /// The fresh block holding the instructions after the call (`None` for an
    /// in-place splice).
    pub continuation: Option<BlockId>,
    /// For each `ret` of the callee, in its block order, and each returned
    /// value of an array return type that is a thin pointer, the fresh value
    /// of its `load` (module documentation, argument and return binding).
    pub returned: Vec<ValueId>,
}

/// The inliner's claim about one caller: the sites, applied in order.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InlineWitness {
    pub sites: Vec<InlineSite>,
}

impl InlineWitness {
    /// Number of claimed rewrites (inlined sites).
    pub fn rewrite_count(&self) -> usize {
        self.sites.len()
    }
}

/// Why a callee cannot be spliced, or `Ok` with its declared signature.
pub(super) fn admit_callee(
    module: &Module,
    caller: FuncId,
    callee: FuncId,
) -> Result<(&Function, &FuncTy), &'static str> {
    if callee == caller {
        return Err("the call is the caller's own");
    }
    let func = module
        .function_by_id(callee)
        .ok_or("the module defines no such function")?;
    if func.is_declaration() {
        return Err("a declaration (no body)");
    }
    if !matches!(
        func.linkage,
        Linkage::External | Linkage::Internal | Linkage::Private
    ) {
        return Err("a linkage another definition may replace at link time");
    }
    if func.attrs.naked {
        return Err("naked");
    }
    if !func.attrs.target_features.is_empty() {
        return Err("it states target features of its own");
    }
    let sig = module
        .func_type(func.ty)
        .ok_or("the callee's function type is missing")?;
    if sig.is_vararg {
        return Err("variadic");
    }
    if func
        .attrs
        .params
        .iter()
        .any(|p| p.byval || matches!(p.pass, Some(PassMode::Indirect { .. })))
    {
        return Err("a parameter passed by copy");
    }
    if !func.proofs.is_empty()
        || func.summary.is_some()
        || func.source_provenance.is_some()
        || func.body_gate.is_some()
        || func
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| !n.proofs.is_empty() || n.proof_context.is_some())
    {
        return Err(
            "it carries proof annotations, call-site proof context, a summary, source \
             provenance or a body gate",
        );
    }
    if !module.spec_modules.is_empty()
        || module.proof_obligations.iter().any(|o| {
            (o.function.is_none() && o.site.is_none())
                || o.function == Some(callee)
                || o.site.as_ref().is_some_and(|s| s.function == callee)
        })
    {
        return Err("a module proof obligation names it (or protects every function)");
    }
    if reaches_itself(module, callee) {
        return Err("recursive");
    }
    check_body_shape(module, func, sig)?;
    Ok((func, sig))
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

/// Every allocation is returned by address or as the typed snapshot above.
/// Its address and constant GEPs are otherwise only plain load/store
/// addresses, never stored values, indices, call/cast operands, branch
/// arguments or compared values.
fn only_return_slots(module: &Module, func: &Function, sig: &FuncTy) -> bool {
    let types = value_types_of(module, func);
    let nodes = || func.blocks.iter().flat_map(|b| &b.body);
    let slots: HashSet<ValueId> = nodes()
        .filter(|n| matches!(n.inst, Inst::Alloca { .. }))
        .flat_map(|n| n.results.iter().copied())
        .collect();
    let constants: HashSet<ValueId> = nodes()
        .filter(|n| matches!(n.inst, Inst::Const { .. }))
        .flat_map(|n| n.results.iter().copied())
        .collect();
    let mut derived: HashSet<ValueId> = slots.clone();
    for node in nodes() {
        if let (Inst::GEP { base, indices, .. }, [result]) = (&node.inst, node.results.as_slice())
            && slots.contains(base)
            && indices.iter().all(|i| constants.contains(i))
        {
            derived.insert(*result);
        }
    }
    let mut returned = HashSet::new();
    for node in nodes() {
        if let Inst::Return { values } = &node.inst {
            for (value, ty) in values.iter().zip(&sig.returns) {
                returned.insert(*value);
                if let Some(slot) = loaded_return_slot(func, *value, ty) {
                    returned.insert(slot);
                }
            }
        }
    }
    if !slots.iter().all(|s| returned.contains(s)) {
        return false;
    }
    nodes().all(|node| {
        let mut ok = true;
        match &node.inst {
            Inst::Load { .. } | Inst::Alloca { .. } => {}
            Inst::Store { value, .. } => ok = !derived.contains(value),
            Inst::GEP { base, indices, .. } => {
                ok = indices.iter().all(|i| !derived.contains(i))
                    && (!slots.contains(base) || node.results.iter().all(|r| derived.contains(r)))
                    && !(derived.contains(base) && !slots.contains(base));
            }
            Inst::Return { values } => {
                ok = values.iter().zip(&sig.returns).all(|(v, t)| {
                    !derived.contains(v)
                        || (slots.contains(v)
                            && types.get(v) != Some(t)
                            && returned_by_address(types.get(v), t))
                });
            }
            other => other.visit_value_operands(|v| ok &= !derived.contains(&v)),
        }
        ok
    })
}

/// A typed return-slot value is consumed only at fixed scalar lanes;
/// it cannot escape to a later iteration or another call as an aggregate.
fn fixed_array_reads(module: &Module, func: &Function, value: ValueId, ty: &Ty) -> bool {
    let Ty::Array(elem, length) = ty else {
        return false;
    };
    let Some(element) = module.ty(*elem) else {
        return false;
    };
    if !(element.is_integer()
        || element.is_float()
        || matches!(element, Ty::Bool | Ty::Char)
        || thin_pointer(element))
    {
        return false;
    }
    func.blocks.iter().flat_map(|b| &b.body).all(|node| {
        let mut used = false;
        node.inst.visit_value_operands(|v| used |= v == value);
        if !used { return true; }
        match &node.inst {
            Inst::ExtractField { ty: have, aggregate, field } => *aggregate == value && have == ty && u64::from(*field) < *length,
            Inst::ExtractElement { ty: have, array, index } if *array == value && module.ty(*elem) == Some(have) => {
                func.blocks.iter().flat_map(|b| &b.body).find(|n| n.results.as_slice() == [*index]).is_some_and(|n|
                    matches!(n.inst, Inst::Const { ty: Ty::Usize, value: Constant::Int(i) } if i >= 0 && u64::try_from(i).is_ok_and(|i| i < *length)))
            }
            _ => false,
        }
    })
}

/// Whether `start` reaches itself through direct calls.
fn reaches_itself(module: &Module, start: FuncId) -> bool {
    let mut seen: HashSet<FuncId> = HashSet::new();
    let mut work: VecDeque<FuncId> = VecDeque::new();
    work.push_back(start);
    while let Some(id) = work.pop_front() {
        let Some(func) = module.function_by_id(id) else {
            continue;
        };
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            if let Some(callee) = direct_callee(&node.inst) {
                if callee == start {
                    return true;
                }
                if seen.insert(callee) {
                    work.push_back(callee);
                }
            }
        }
    }
    false
}

/// The function a direct-call form names.
fn direct_callee(inst: &Inst) -> Option<FuncId> {
    match inst {
        Inst::Call { callee, .. }
        | Inst::CallCannotUnwind { callee, .. }
        | Inst::Invoke { callee, .. } => Some(*callee),
        _ => None,
    }
}

/// The instructions a spliced body may contain (an allowlist: a form not
/// named here is never spliced).
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

/// A thin pointer type: one address word, no metadata.
fn thin_pointer(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

/// The terminators a spliced body may end a block with.
fn splice_terminator(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Return { .. }
            | Inst::Unreachable
    )
}

/// The callee body's shape (module documentation).
fn check_body_shape(module: &Module, func: &Function, sig: &FuncTy) -> Result<(), &'static str> {
    let entry = func
        .blocks
        .iter()
        .find(|b| b.id == func.entry)
        .ok_or("the callee has no entry block")?;
    if entry.params.len() != sig.params.len()
        || entry
            .params
            .iter()
            .zip(&sig.params)
            .any(|((_, t), p)| t != p && !(thin_pointer(t) && thin_pointer(p)))
    {
        return Err(
            "the entry parameters are not the declared parameters (or thin pointers of other \
             pointer types)",
        );
    }
    let types = value_types_of(module, func);
    let mut returns = 0usize;
    let mut ids = HashSet::new();
    for block in &func.blocks {
        if !ids.insert(block.id) {
            return Err("two blocks share an id");
        }
        let Some((last, body)) = block.body.split_last() else {
            return Err("an empty block");
        };
        if !splice_terminator(&last.inst) || body.iter().any(|n| n.inst.is_terminator()) {
            return Err(
                "a block does not end in exactly one br, condbr, switch, ret or unreachable",
            );
        }
        if block.body.iter().any(|n| !spliceable(&n.inst)) {
            return Err("an instruction outside the splice allowlist");
        }
        for edge in last.inst.successor_edges() {
            if edge.target == func.entry {
                return Err("the entry block is the target of an edge");
            }
        }
        if let Inst::Return { values } = &last.inst {
            returns += 1;
            if values.len() != sig.returns.len()
                || values
                    .iter()
                    .zip(&sig.returns)
                    .any(|(v, t)| types.get(v) != Some(t) && !returned_by_address(types.get(v), t))
            {
                return Err("a ret whose values are not of the declared return types");
            }
        }
    }
    for block in &func.blocks {
        if let Some(last) = block.body.last() {
            for edge in last.inst.successor_edges() {
                if !ids.contains(&edge.target) {
                    return Err("an edge to a block the callee does not have");
                }
            }
        }
    }
    if returns == 0 {
        return Err("no block returns");
    }
    Ok(())
}

/// Whether a value of type `have` stands for an aggregate of the array
/// type `want` by its address: a thin pointer where an array is passed or
/// returned (module documentation, argument and return binding).
fn returned_by_address(have: Option<&Ty>, want: &Ty) -> bool {
    have.is_some_and(thin_pointer) && matches!(want, Ty::Array(..))
}

/// This module's typing of `func`'s values: block parameters, the
/// single-result forms whose result type is a field of the instruction, and
/// the results of a direct call (its callee's declared returns). `None` for every other form, which a check needing it refuses.
pub(super) fn value_types_of(module: &Module, func: &Function) -> HashMap<ValueId, Ty> {
    let mut types = HashMap::new();
    for block in &func.blocks {
        for (value, ty) in &block.params {
            types.insert(*value, ty.clone());
        }
        for node in &block.body {
            if let Inst::Call { callee, .. } = &node.inst {
                if let Some(sig) = module
                    .function_by_id(*callee)
                    .and_then(|f| module.func_type(f.ty))
                    && sig.returns.len() == node.results.len()
                {
                    for (value, ty) in node.results.iter().zip(&sig.returns) {
                        types.insert(*value, ty.clone());
                    }
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
                | Inst::BinOp { ty, .. }
                | Inst::UnOp { ty, .. } => ty.clone(),
                Inst::Cast { dst_ty, .. } => dst_ty.clone(),
                Inst::ICmp { .. } | Inst::FCmp { .. } => Ty::Bool,
                Inst::Alloca { .. }
                | Inst::GEP { .. }
                | Inst::GlobalAddr { .. }
                | Inst::NullPtr => Ty::Ptr,
                _ => continue,
            };
            types.insert(*result, ty);
        }
    }
    types
}

/// Every value `func` names: parameters, results, operands and debug names.
fn value_universe(func: &Function) -> HashSet<ValueId> {
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

/// Whether block `id` of `func` lies on a cycle (it reaches itself).
fn on_cycle(func: &Function, id: BlockId) -> bool {
    let positions = block_positions(func);
    let successors = |b: BlockId| -> Vec<BlockId> {
        positions
            .get(&b)
            .and_then(|&i| func.blocks[i].body.last())
            .map(|n| n.inst.successor_edges().iter().map(|e| e.target).collect())
            .unwrap_or_default()
    };
    let mut seen = HashSet::new();
    let mut work: Vec<BlockId> = successors(id);
    while let Some(b) = work.pop() {
        if b == id {
            return true;
        }
        if seen.insert(b) {
            work.extend(successors(b));
        }
    }
    false
}

/// `inst` with its block targets moved through `map`.
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

/// A cloned callee node: renamed operands, results and targets, the callee's
/// span, no scope and no proof (the callee carries none).
fn clone_node(
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

/// A binding node at the call site: the call's span and scope.
fn site_node(call: &InstrNode, inst: Inst, results: Vec<ValueId>) -> InstrNode {
    InstrNode {
        inst,
        results,
        proofs: Vec::new(),
        span: call.span,
        proof_context: None,
        scope: call.scope,
    }
}

/// The binding of one `ret` of the callee: the loads of the values it
/// returns by address (`loads`, each `(position, fresh value)`), then copies
/// into the results and `br` to the continuation (one returning block), or
/// `br` passing the returned values (several); in place (no continuation),
/// the loads and copies alone.
fn bind_return(
    call: &InstrNode,
    values: &[ValueId],
    loads: &[(usize, ValueId)],
    results: &[ValueId],
    returns: &[Ty],
    continuation: Option<BlockId>,
    joined: bool,
) -> Vec<InstrNode> {
    let mut out = Vec::new();
    let mut values = values.to_vec();
    for &(position, loaded) in loads {
        out.push(site_node(
            call,
            Inst::Load {
                ty: returns[position].clone(),
                ptr: values[position],
                volatile: false,
                align: Some(1),
            },
            vec![loaded],
        ));
        values[position] = loaded;
    }
    let values = values.as_slice();
    if joined {
        if let Some(target) = continuation {
            out.push(site_node(
                call,
                Inst::Br {
                    target,
                    args: values.to_vec(),
                },
                Vec::new(),
            ));
        }
        return out;
    }
    for ((value, result), ty) in values.iter().zip(results).zip(returns) {
        out.push(site_node(
            call,
            Inst::Copy {
                ty: ty.clone(),
                operand: *value,
            },
            vec![*result],
        ));
    }
    if let Some(target) = continuation {
        out.push(site_node(
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

/// The opcode key of `inst` for the conservation check: operands abstracted
/// to `%0`, and `br`/`condbr`/`switch` keyed by their shape alone, so the
/// renaming and the retargeting a splice performs keep every key (the OPT-4
/// inliner's `mb_opcode_key`). A call keeps its callee.
fn opcode_key(inst: &Inst) -> String {
    match inst {
        Inst::Br { args, .. } => format!("br/{}", args.len()),
        Inst::CondBr {
            then_args,
            else_args,
            ..
        } => format!("condbr/{}/{}", then_args.len(), else_args.len()),
        Inst::Switch {
            cases,
            default_args,
            exhaustive_enum_unreachable,
            ..
        } => {
            let shape: Vec<String> = cases
                .iter()
                .map(|c| format!("{:?}/{}", c.value, c.args.len()))
                .collect();
            format!(
                "switch/{}/{}/{exhaustive_enum_unreachable}",
                shape.join(","),
                default_args.len()
            )
        }
        _ => {
            let mut abstracted = inst.clone();
            let mut map = HashMap::new();
            inst.visit_value_operands(|v| {
                map.insert(v, ValueId::new(0));
            });
            trust_ir::mem2reg::rewrite_inst(&mut abstracted, &map);
            format!("{abstracted:?}")
        }
    }
}

/// The opcode multiset of `func`.
fn opcode_multiset(func: &Function) -> BTreeMap<String, i64> {
    let mut m = BTreeMap::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        *m.entry(opcode_key(&node.inst)).or_insert(0) += 1;
    }
    m
}

/// The OPT-4 conservation check: `actual` equals `expected` key by key.
fn verify_opcode_conservation(
    actual: &BTreeMap<String, i64>,
    expected: &BTreeMap<String, i64>,
) -> Result<(), MidTvError> {
    let keys: HashSet<&String> = actual.keys().chain(expected.keys()).collect();
    let mut keys: Vec<&String> = keys.into_iter().collect();
    keys.sort();
    for key in keys {
        let a = actual.get(key).copied().unwrap_or(0);
        let e = expected.get(key).copied().unwrap_or(0);
        if a != e {
            return Err(MidTvError::NotConserved {
                detail: format!(
                    "{key}: {a} in the target, {e} expected (an instruction was dropped or \
                     duplicated)"
                ),
            });
        }
    }
    Ok(())
}

/// The OPT-4 CFG well-formedness check on the target, plus single
/// definitions: the source's entry, unique block ids, each block non-empty
/// and ending in its only terminator, every edge to an existing block, every
/// value defined once.
fn verify_cfg_wellformed(source: &Function, target: &Function) -> Result<(), MidTvError> {
    let bad = |detail: String| Err(MidTvError::MalformedCfg { detail });
    if target.entry != source.entry {
        return bad(format!(
            "the entry moved from {} to {}",
            source.entry, target.entry
        ));
    }
    let mut ids = HashSet::new();
    for block in &target.blocks {
        if !ids.insert(block.id) {
            return bad(format!("block id {} is used twice", block.id));
        }
    }
    if !ids.contains(&target.entry) {
        return bad("the entry block is missing".to_string());
    }
    let mut defined = HashSet::new();
    for block in &target.blocks {
        let Some((last, body)) = block.body.split_last() else {
            return bad(format!("block {} is empty", block.id));
        };
        if !last.inst.is_terminator() {
            return bad(format!("block {} does not end in a terminator", block.id));
        }
        if body.iter().any(|n| n.inst.is_terminator()) {
            return bad(format!(
                "block {} has a terminator before its end",
                block.id
            ));
        }
        for edge in last.inst.successor_edges() {
            if !ids.contains(&edge.target) {
                return bad(format!(
                    "block {} branches to {}, which does not exist",
                    block.id, edge.target
                ));
            }
        }
        for value in block
            .params
            .iter()
            .map(|(v, _)| *v)
            .chain(block.body.iter().flat_map(|n| n.results.iter().copied()))
        {
            if !defined.insert(value) {
                return bad(format!("%{value} is defined twice"));
            }
        }
    }
    Ok(())
}

/// Apply one site to `cur`, checking its side conditions, and move
/// `expected` (the opcode multiset the target must have) by the call it
/// removes and the instructions it adds.
fn apply_site(
    module: &Module,
    cur: &mut Function,
    at: usize,
    site: &InlineSite,
    expected: &mut BTreeMap<String, i64>,
    spliced_slot_bytes: &mut u64,
) -> Result<(), MidTvError> {
    let refuse = |why: &str| MidTvError::NotInlinable {
        site: at,
        why: why.to_string(),
    };
    let positions = block_positions(cur);
    let bi = *positions
        .get(&site.block)
        .ok_or_else(|| refuse("the site's block does not exist"))?;
    let call = cur.blocks[bi]
        .body
        .get(site.index)
        .ok_or_else(|| refuse("the site's block has no such instruction"))?
        .clone();
    let Inst::Call { callee, args } = &call.inst else {
        return Err(refuse("the instruction is not a direct call"));
    };
    if *callee != site.callee {
        return Err(refuse("the call names another callee"));
    }
    let (callee_fn, sig) = admit_callee(module, cur.id, *callee).map_err(refuse)?;
    if call.results.len() != sig.returns.len() || args.len() != sig.params.len() {
        return Err(MidTvError::WrongBinding {
            site: at,
            why: "the call's arity is not the callee's".to_string(),
        });
    }
    if !call.proofs.is_empty() || call.proof_context.is_some() {
        return Err(refuse(
            "the call carries a proof annotation or proof context",
        ));
    }
    let entry = callee_fn
        .blocks
        .iter()
        .find(|b| b.id == callee_fn.entry)
        .ok_or_else(|| refuse("the callee has no entry block"))?;
    // ---- Argument binding: each parameter is bound to its argument, or, when
    // the argument is a thin pointer of another pointer type, to a fresh
    // `ptrtoptr` of it.
    if site.params.len() != entry.params.len()
        || site
            .params
            .iter()
            .zip(&entry.params)
            .any(|((p, _), (q, _))| p != q)
    {
        return Err(MidTvError::WrongBinding {
            site: at,
            why: "the claimed binding does not name the entry parameters in order".to_string(),
        });
    }
    let caller_types = value_types_of(module, cur);
    let universe = value_universe(cur);
    // Each binding node: `ptrtoptr` of a thin pointer to another pointer
    // type, or the `load` of an array passed by its address.
    let mut casts: Vec<(ValueId, Inst)> = Vec::new();
    for (((_, bound), arg), (_, ty)) in site.params.iter().zip(args).zip(&entry.params) {
        let arg_ty = caller_types.get(arg);
        if bound == arg {
            if arg_ty != Some(ty) {
                return Err(MidTvError::WrongBinding {
                    site: at,
                    why: format!("argument %{arg} is not of the parameter's type {ty}"),
                });
            }
            continue;
        }
        match arg_ty {
            Some(from) if thin_pointer(from) && thin_pointer(ty) && from != ty => {
                casts.push((
                    *bound,
                    Inst::Cast {
                        op: CastOp::PtrToPtr,
                        src_ty: from.clone(),
                        dst_ty: ty.clone(),
                        operand: *arg,
                    },
                ));
            }
            from if returned_by_address(from, ty) => {
                casts.push((
                    *bound,
                    Inst::Load {
                        ty: ty.clone(),
                        ptr: *arg,
                        volatile: false,
                        align: Some(1),
                    },
                ));
            }
            _ => {
                return Err(MidTvError::WrongBinding {
                    site: at,
                    why: format!(
                        "%{bound} is bound in place of argument %{arg}, which is neither a thin \
                         pointer of another pointer type than the parameter's {ty} nor a thin \
                         pointer to an array the parameter is"
                    ),
                });
            }
        }
    }
    // ---- The stack bound.
    let slots: Vec<(BlockId, &Ty)> = callee_fn
        .blocks
        .iter()
        .flat_map(|b| b.body.iter().map(move |n| (b.id, n)))
        .filter_map(|(block, n)| match &n.inst {
            Inst::Alloca { ty, .. } => Some((block, ty)),
            _ => None,
        })
        .collect();
    if !slots.is_empty() {
        if slots.iter().any(|&(block, _)| on_cycle(callee_fn, block)) {
            return Err(refuse(
                "the callee allocates on a cycle of its own, which the splice puts on a cycle \
                 of the caller",
            ));
        }
        if on_cycle(cur, site.block)
            && callee_fn.blocks.iter().flat_map(|b| &b.body).any(|node| {
                let Inst::Return { values } = &node.inst else {
                    return false;
                };
                values
                    .iter()
                    .zip(&sig.returns)
                    .enumerate()
                    .any(|(k, (value, ty))| {
                        loaded_return_slot(callee_fn, *value, ty).is_some()
                            && !fixed_array_reads(module, cur, call.results[k], ty)
                    })
            })
        {
            return Err(refuse(
                "a typed return-slot value escapes its fixed scalar lane reads",
            ));
        }
        if on_cycle(cur, site.block) && !only_return_slots(module, callee_fn, sig) {
            return Err(refuse(
                "the callee allocates a slot other than a return slot and the call's block lies \
                 on a cycle of the caller",
            ));
        }
        if reaches_itself(module, cur.id) {
            return Err(refuse(
                "the callee allocates and the caller reaches itself through direct calls",
            ));
        }
        let mut bytes = *spliced_slot_bytes;
        for (_, ty) in slots {
            let size = module
                .ty_layout_shape(ty)
                .ok()
                .and_then(|shape| shape.size_bytes())
                .ok_or_else(|| refuse("the size of a callee slot is unknown"))?;
            bytes = bytes.saturating_add(size);
        }
        if bytes > MAX_SPLICED_SLOT_BYTES {
            return Err(refuse(&format!(
                "the slots spliced into the caller would total {bytes} bytes, over \
                 {MAX_SPLICED_SLOT_BYTES}"
            )));
        }
        *spliced_slot_bytes = bytes;
    }
    let in_place = site.blocks.is_empty();
    if in_place != site.continuation.is_none() {
        return Err(refuse(
            "a continuation is claimed exactly when callee blocks are",
        ));
    }
    if in_place
        && !(callee_fn.blocks.len() == 1
            && matches!(
                callee_fn.blocks[0].body.last().map(|n| &n.inst),
                Some(Inst::Return { .. })
            ))
    {
        return Err(refuse(
            "an in-place splice needs a one-block callee that returns",
        ));
    }
    // ---- Fresh renaming.
    let fresh_err = |why: String| MidTvError::NotFresh { site: at, why };
    let mut callee_values: Vec<ValueId> = Vec::new();
    for block in &callee_fn.blocks {
        if block.id != callee_fn.entry {
            callee_values.extend(block.params.iter().map(|(v, _)| *v));
        }
        for node in &block.body {
            callee_values.extend(node.results.iter().copied());
        }
    }
    let claimed: Vec<ValueId> = site.values.iter().map(|(c, _)| *c).collect();
    if claimed != callee_values {
        return Err(fresh_err(
            "the renamed values are not the callee's values in block order".to_string(),
        ));
    }
    // The values each `ret` returns by address, in the callee's block order,
    // and the fresh loads the witness names for them.
    let callee_types = value_types_of(module, callee_fn);
    let mut by_address: Vec<Vec<usize>> = Vec::new();
    for block in &callee_fn.blocks {
        if let Some(Inst::Return { values }) = block.body.last().map(|n| &n.inst) {
            by_address.push(
                values
                    .iter()
                    .zip(&sig.returns)
                    .enumerate()
                    .filter(|(_, (v, t))| {
                        callee_types.get(v) != Some(t)
                            && returned_by_address(callee_types.get(v), t)
                    })
                    .map(|(position, _)| position)
                    .collect(),
            );
        }
    }
    if by_address.iter().map(Vec::len).sum::<usize>() != site.returned.len() {
        return Err(MidTvError::WrongBinding {
            site: at,
            why: "the witness does not name one load per value returned by address".to_string(),
        });
    }
    let mut ret_loads: VecDeque<Vec<(usize, ValueId)>> = VecDeque::new();
    let mut named = site.returned.iter().copied();
    for positions in &by_address {
        ret_loads.push_back(
            positions
                .iter()
                .map(|&p| (p, named.next().expect("counted above")))
                .collect(),
        );
    }
    let mut images = HashSet::new();
    for fresh in site
        .values
        .iter()
        .map(|(_, f)| f)
        .chain(casts.iter().map(|(b, _)| b))
        .chain(site.returned.iter())
    {
        if universe.contains(fresh) || !images.insert(*fresh) {
            return Err(fresh_err(format!(
                "%{fresh} is already named by the caller or claimed twice"
            )));
        }
    }
    let mut value_map: HashMap<ValueId, ValueId> = site.values.iter().copied().collect();
    value_map.extend(site.params.iter().copied());
    let cast_nodes: Vec<InstrNode> = casts
        .iter()
        .map(|(bound, inst)| site_node(&call, inst.clone(), vec![*bound]))
        .collect();
    let mut block_map: HashMap<BlockId, BlockId> = HashMap::new();
    if !in_place {
        let callee_blocks: Vec<BlockId> = callee_fn.blocks.iter().map(|b| b.id).collect();
        let claimed: Vec<BlockId> = site.blocks.iter().map(|(c, _)| *c).collect();
        if claimed != callee_blocks {
            return Err(fresh_err(
                "the renamed blocks are not the callee's blocks in order".to_string(),
            ));
        }
        let existing: HashSet<BlockId> = cur.blocks.iter().map(|b| b.id).collect();
        let mut fresh_blocks = HashSet::new();
        for id in site.blocks.iter().map(|(_, n)| *n).chain(site.continuation) {
            if existing.contains(&id) || !fresh_blocks.insert(id) {
                return Err(fresh_err(format!(
                    "block {id} already exists or is claimed twice"
                )));
            }
        }
        block_map = site.blocks.iter().copied().collect();
    }
    // ---- Rebuild.
    let rets = callee_fn
        .blocks
        .iter()
        .filter(|b| matches!(b.body.last().map(|n| &n.inst), Some(Inst::Return { .. })))
        .count();
    let joined = rets > 1;
    *expected.entry(opcode_key(&call.inst)).or_insert(0) -= 1;
    for node in callee_fn.blocks.iter().flat_map(|b| &b.body) {
        if !matches!(node.inst, Inst::Return { .. }) {
            *expected.entry(opcode_key(&node.inst)).or_insert(0) += 1;
        }
    }
    let results = call.results.clone();
    let count = |nodes: &[InstrNode], expected: &mut BTreeMap<String, i64>| {
        for node in nodes {
            *expected.entry(opcode_key(&node.inst)).or_insert(0) += 1;
        }
    };
    if in_place {
        let block = &callee_fn.blocks[0];
        let (last, body) = block.body.split_last().expect("checked non-empty");
        let Inst::Return { values } = &last.inst else {
            unreachable!("checked: the one block returns");
        };
        count(&cast_nodes, expected);
        let mut spliced: Vec<InstrNode> = cast_nodes;
        spliced.extend(body.iter().map(|n| clone_node(n, &value_map, &block_map)));
        let renamed: Vec<ValueId> = values
            .iter()
            .map(|v| *value_map.get(v).unwrap_or(v))
            .collect();
        let loads = ret_loads.pop_front().unwrap_or_default();
        let binding = bind_return(&call, &renamed, &loads, &results, &sig.returns, None, false);
        count(&binding, expected);
        spliced.extend(binding);
        cur.blocks[bi].body.splice(site.index..=site.index, spliced);
        return Ok(());
    }
    let continuation = site.continuation.expect("checked");
    let entry_copy = block_map[&callee_fn.entry];
    let tail: Vec<InstrNode> = cur.blocks[bi].body.split_off(site.index + 1);
    cur.blocks[bi].body.pop();
    let jump = site_node(
        &call,
        Inst::Br {
            target: entry_copy,
            args: Vec::new(),
        },
        Vec::new(),
    );
    count(&cast_nodes, expected);
    count(std::slice::from_ref(&jump), expected);
    cur.blocks[bi].body.extend(cast_nodes);
    cur.blocks[bi].body.push(jump);
    let mut new_blocks: Vec<Block> = Vec::new();
    for block in &callee_fn.blocks {
        let mut out = Block::new(block_map[&block.id]);
        if block.id != callee_fn.entry {
            out.params = block
                .params
                .iter()
                .map(|(v, t)| (value_map[v], t.clone()))
                .collect();
        }
        for node in &block.body {
            if let Inst::Return { values } = &node.inst {
                let renamed: Vec<ValueId> = values
                    .iter()
                    .map(|v| *value_map.get(v).unwrap_or(v))
                    .collect();
                let loads = ret_loads.pop_front().unwrap_or_default();
                let binding = bind_return(
                    &call,
                    &renamed,
                    &loads,
                    &results,
                    &sig.returns,
                    Some(continuation),
                    joined,
                );
                count(&binding, expected);
                out.body.extend(binding);
            } else {
                out.body.push(clone_node(node, &value_map, &block_map));
            }
        }
        new_blocks.push(out);
    }
    let mut cont = Block::new(continuation);
    if joined {
        cont.params = results
            .iter()
            .copied()
            .zip(sig.returns.iter().cloned())
            .collect();
    }
    cont.body = tail;
    new_blocks.push(cont);
    let at_pos = bi + 1;
    cur.blocks.splice(at_pos..at_pos, new_blocks);
    Ok(())
}

/// Apply every site of `witness` to `source` (module documentation): the
/// rebuilt caller and the opcode multiset its target must have.
fn apply_sites(
    module: &Module,
    source: &Function,
    witness: &InlineWitness,
) -> Result<(Function, BTreeMap<String, i64>), MidTvError> {
    if witness.sites.is_empty() {
        return Err(MidTvError::NotInlinable {
            site: 0,
            why: "the witness claims no site".to_string(),
        });
    }
    let mut cur = source.clone();
    let mut expected = opcode_multiset(source);
    let mut spliced_slot_bytes = 0u64;
    for (at, site) in witness.sites.iter().enumerate() {
        apply_site(
            module,
            &mut cur,
            at,
            site,
            &mut expected,
            &mut spliced_slot_bytes,
        )?;
    }
    expected.retain(|_, n| *n != 0);
    Ok((cur, expected))
}

/// Rebuild the inlined caller from `source` and `witness`, after checking
/// the TARGET's CFG, single definitions and opcode conservation (module
/// documentation); the caller compares the rebuild with the target.
pub(super) fn rebuild_inline(
    module: &Module,
    source: &Function,
    target: &Function,
    witness: &InlineWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let (rebuilt, expected) = apply_sites(module, source, witness)?;
    verify_cfg_wellformed(source, target)?;
    verify_opcode_conservation(&opcode_multiset(target), &expected)?;
    Ok((
        rebuilt,
        WitnessVerdict {
            exact: 0,
            refinements: witness.sites.len(),
        },
    ))
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_inline_tests.rs"]
mod tests;
