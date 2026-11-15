// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! WS7.3-pre: spell the MIR lane's ABI edges in valid trust-ir.
//!
//! The MIR lane keeps a by-value aggregate (a Rust struct, tuple, `Option`, a
//! slice's `{ data, len }` image, ...) in a stack SLOT and names it by the
//! slot's address, a plain `Ptr`. Its callees, however, are DECLARED with the
//! aggregate type (`func_ty_for_instance` gives a by-value aggregate parameter
//! or return its lane tuple / lane array), and a reference parameter with its
//! reference type. Until now the lane passed the slot address where the
//! declaration names the aggregate, and a `Ptr` where it names `&T`, and relied
//! on the trust-cg adapter's private reading of that mismatch (an aggregate
//! value IS the address of its bytes there). trust-ir defines neither: the
//! validator refuses the call (`CallArgTypeMismatch`), the return
//! (`ReturnTypeMismatch`) and the entry block (`EntryParamsMismatch`), so every
//! trust-cg ingestion entry that validates (WS7.3) would refuse the lane's
//! output for ordinary Rust.
//!
//! [`legalize_abi_edges`] makes each such edge say what it means, with types
//! read from the function and its module (never guessed):
//!
//! * **A slot address where the declaration names a lane aggregate** (an
//!   argument of a `Call` / `Invoke` / `CallIndirect` / `InvokeIndirect`, or a
//!   `Return` value, whose own type is exactly `Ptr` while the declared type is
//!   a `Tuple` or an `Array`): the aggregate VALUE is loaded from the slot
//!   (`load <declared> , ptr %slot`) and passed instead. That is the value the
//!   adapter read through the address, now read by an explicit `Load` at the
//!   edge, so the callee receives a copy it owns — Rust's by-value semantics —
//!   rather than the caller's storage.
//! * **A thin address of another thin-pointer type** (`Ptr` where `&T` is
//!   declared, `&mut T` where `*mut T` is, ...): an explicit `PtrToPtr` to the
//!   declared type ([`can_retype_thin_address`], the rule
//!   `canonicalize_copies` already applies to `Copy`s and branch edges). On an
//!   ENTRY block parameter the parameter takes the declared type and its old
//!   value is re-defined from it by a `PtrToPtr` at the top of the entry block,
//!   so every use keeps the type it was lowered against.
//! * **A runtime code address called through a `reify_fn_pointer` cast** (a
//!   `fn(..)` pointer value, a vtable or drop-glue slot): trust-ir defines that
//!   cast only from a function item, and its indirect call takes a pointer
//!   callee, so the call takes the address itself; a cast whose result is also
//!   used otherwise (handed to the typed `indirect_unwind` thunk) is re-spelled
//!   as the `ptrtoptr ptr to Func(sig)` re-type trust-ir defines
//!   ([`call_through_code_addresses`]).
//!
//! Anything else — a fat pointer, an aggregate passed as something else, a
//! width change, a value whose type cannot be read — is left exactly as it
//! was, so the validator still reports it and a validating entry still refuses
//! it. The pass grants no authority, infers no lifetime or aliasing fact, and
//! changes no address: `PtrToPtr` lowers to the same register move a `Copy`
//! does, and the inserted `Load` reads the bytes the adapter read before.

use std::collections::HashMap;

use trust_ir::{
    CastOp, Constant, FuncId, FuncTyId, Function, Inst, InstrNode, Module, Ty, ValueId,
};

use crate::pointer_casts::can_retype_thin_address;

/// Whether `ty` is a lane aggregate the MIR lane carries by its slot address: a
/// `Tuple` or an `Array` (the lane tuple / lane array `func_ty_for_instance`
/// declares for a by-value aggregate). Nothing else is reinterpreted.
fn is_slot_carried_aggregate(ty: &Ty) -> bool {
    matches!(ty, Ty::Tuple(fields) if !fields.is_empty()) || matches!(ty, Ty::Array(_, n) if *n > 0)
}

/// The value types of `func`: block parameters and every instruction's declared
/// result types (`InstrNode::result_tys`). A self-call reads `func`'s own
/// signature, which `module` may not hold yet.
fn value_types(func: &Function, module: &Module) -> HashMap<ValueId, Ty> {
    let mut tys = HashMap::new();
    for block in &func.blocks {
        for (value, ty) in &block.params {
            tys.insert(*value, ty.clone());
        }
        for node in &block.body {
            let result_tys = match &node.inst {
                Inst::Call { callee, .. }
                | Inst::CallCannotUnwind { callee, .. }
                | Inst::Invoke { callee, .. }
                    if *callee == func.id && module.function_by_id(*callee).is_none() =>
                {
                    module
                        .func_type(func.ty)
                        .map(|sig| sig.returns.clone())
                        .unwrap_or_default()
                }
                _ => node.result_tys(module),
            };
            for (value, ty) in node.results.iter().zip(result_tys) {
                tys.insert(*value, ty);
            }
        }
    }
    tys
}

/// The declared parameter types of a call's callee, or the function's own
/// return types for a `Return`; `None` for every other instruction (and for a
/// callee whose signature the module does not hold).
fn declared_edge_types(inst: &Inst, func: &Function, module: &Module) -> Option<Vec<Ty>> {
    let sig = |callee| {
        let ty = if callee == func.id {
            Some(func.ty)
        } else {
            module.function_by_id(callee).map(|f| f.ty)
        }?;
        module.func_type(ty).map(|sig| sig.params.clone())
    };
    match inst {
        Inst::Call { callee, .. }
        | Inst::CallCannotUnwind { callee, .. }
        | Inst::Invoke { callee, .. } => sig(*callee),
        Inst::CallIndirect { sig, .. }
        | Inst::CallIndirectCannotUnwind { sig, .. }
        | Inst::InvokeIndirect { sig, .. } => module.func_type(*sig).map(|sig| sig.params.clone()),
        Inst::Return { .. } => module.func_type(func.ty).map(|sig| sig.returns.clone()),
        _ => None,
    }
}

/// The values `declared_edge_types` describes, in the same order.
fn edge_values_mut(inst: &mut Inst) -> Option<&mut Vec<ValueId>> {
    match inst {
        Inst::Call { args, .. }
        | Inst::CallCannotUnwind { args, .. }
        | Inst::Invoke { args, .. }
        | Inst::CallIndirect { args, .. }
        | Inst::CallIndirectCannotUnwind { args, .. }
        | Inst::InvokeIndirect { args, .. } => Some(args),
        Inst::Return { values } => Some(values),
        _ => None,
    }
}

/// How the edge value `value: have` is re-spelled for its declared type
/// `want`, if at all.
fn edge_conversion(value: ValueId, have: &Ty, want: &Ty) -> Option<Inst> {
    if have == want {
        return None;
    }
    if can_retype_thin_address(have, want) {
        return Some(Inst::Cast {
            op: CastOp::PtrToPtr,
            src_ty: have.clone(),
            dst_ty: want.clone(),
            operand: value,
        });
    }
    if *have == Ty::Ptr && is_slot_carried_aggregate(want) {
        return Some(Inst::Load {
            ty: want.clone(),
            ptr: value,
            volatile: false,
            align: None,
        });
    }
    None
}

/// One past the largest `ValueId` `func` defines or uses: the first value a
/// rewrite of `func` may define.
fn first_free_value(func: &Function) -> u32 {
    let mut next = 0u32;
    let mut see = |value: ValueId| next = next.max(value.index().saturating_add(1));
    for block in &func.blocks {
        for (value, _) in &block.params {
            see(*value);
        }
        for node in &block.body {
            for result in &node.results {
                see(*result);
            }
            node.inst.visit_value_operands(&mut see);
        }
    }
    next
}

/// Legalize every function DEFINED in `module` against the module itself: the
/// reinterpreting `Copy`s, branch edges and constants
/// (`canonicalize_copies::canonicalize_reinterpret_copies`, here with every
/// value typed through the module's own declarations), then the call / return
/// / entry edges ([`legalize_abi_edges`]).
///
/// The bridge runs this on the module it hands to the compiler, after the
/// per-codegen-unit merge: the merge re-binds call edges to one unified
/// declaration (`__rust_alloc` returns `ptr` there, `*mut u8` in a function's
/// own lowering-time view), so only the merged module's types say what each
/// edge must carry. Each function is taken out of the module while it is
/// rewritten and a declaration with the same id, name and signature stands in
/// for it, so its self-calls and every other call still resolve.
///
/// A function some proof obligation is SITED in (`ObligationSite` names a
/// block and an instruction INDEX) is left exactly as it was: inserting a node
/// would move the instruction the obligation is about. The bridge emits no
/// obligations today; this keeps a future one bound to its node.
pub(crate) fn legalize_module(module: &mut Module) {
    let sited: std::collections::HashSet<trust_ir::FuncId> = module
        .proof_obligations
        .iter()
        .filter_map(|obligation| obligation.site.map(|site| site.function))
        .collect();
    for index in 0..module.functions.len() {
        if module.functions[index].blocks.is_empty() || sited.contains(&module.functions[index].id)
        {
            continue;
        }
        let stand_in = {
            let func = &module.functions[index];
            Function::new(func.id, func.name.clone(), func.ty, func.entry)
        };
        let mut func = std::mem::replace(&mut module.functions[index], stand_in);
        let mut next = first_free_value(&func);
        let mut fresh = || {
            let value = ValueId::new(next);
            next += 1;
            value
        };
        crate::canonicalize_copies::canonicalize_reinterpret_copies(
            &mut func,
            Some(module),
            &mut fresh,
        );
        // Here and not at lowering: the field-store gate has already judged
        // every recorded field store as lowered (`retype_stored_and_selected_values`).
        crate::canonicalize_copies::retype_stored_and_selected_values(
            &mut func,
            Some(module),
            &mut fresh,
        );
        legalize_abi_edges(&mut func, module, &mut fresh);
        drop_unreachable_stubs(&mut func);
        module.functions[index] = func;
    }
}

/// Remove the blocks the lowering's dead-block pass reduced to a bare
/// `unreachable` stub (no parameters, no other instruction) when no path from
/// the entry reaches them. trust-ir refuses an unreachable block
/// (`UnreachableBlock`); the stub holds no value and no instruction, and no
/// reachable block branches to it, so nothing observes its removal. A block
/// with any other content is left for the validator to report.
fn drop_unreachable_stubs(func: &mut Function) {
    let by_id: HashMap<trust_ir::BlockId, usize> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| (block.id, index))
        .collect();
    if !by_id.contains_key(&func.entry) {
        return;
    }
    let mut reachable = std::collections::HashSet::from([func.entry]);
    let mut worklist = vec![func.entry];
    while let Some(id) = worklist.pop() {
        let Some(terminator) = by_id
            .get(&id)
            .and_then(|index| func.blocks[*index].terminator())
        else {
            continue;
        };
        for edge in terminator.inst.successor_edges() {
            if reachable.insert(edge.target) {
                worklist.push(edge.target);
            }
        }
    }
    func.blocks.retain(|block| {
        reachable.contains(&block.id)
            || !(block.params.is_empty()
                && block.body.len() == 1
                && matches!(block.body[0].inst, Inst::Unreachable))
    });
}

/// Re-spell every call argument, return value and entry parameter of `func`
/// whose type differs from its declaration in one of the two ways the module
/// doc names. `fresh` allocates new values from the function's own counter.
pub(crate) fn legalize_abi_edges(
    func: &mut Function,
    module: &Module,
    mut fresh: impl FnMut() -> ValueId,
) {
    let val_ty = value_types(func, module);
    for index in 0..func.blocks.len() {
        let body = std::mem::take(&mut func.blocks[index].body);
        let mut out = Vec::with_capacity(body.len());
        for mut node in body {
            let declared = declared_edge_types(&node.inst, func, module);
            // An edge whose arity disagrees with its declaration is a different
            // defect, left for the validator to report.
            if let (Some(declared), Some(values)) = (declared, edge_values_mut(&mut node.inst)) {
                if values.len() == declared.len() {
                    for (value, want) in values.iter_mut().zip(&declared) {
                        let Some(inst) = val_ty
                            .get(value)
                            .and_then(|have| edge_conversion(*value, have, want))
                        else {
                            continue;
                        };
                        let result = fresh();
                        out.push(InstrNode::new(inst).with_result(result));
                        *value = result;
                    }
                }
            }
            out.push(node);
        }
        func.blocks[index].body = out;
    }
    legalize_entry_params(func, module, &mut fresh);
    call_through_code_addresses(func);
    // After the code-address pass: that pass matches a `ptr -> Func(sig)`
    // re-typing to its call by the call's ORIGINAL signature id.
    call_fn_items_at_their_own_signature(func, module);
}

/// The function ITEM an indirect callee is, when its provenance is a `FnDef`
/// constant reached through `reify_fn_pointer` casts and `Copy`s inside the
/// function. Bounded by the definition count, so a malformed cyclic chain ends.
fn fn_item_callee(
    definitions: &HashMap<ValueId, &Inst>,
    mut value: ValueId,
) -> Option<(FuncId, FuncTyId)> {
    for _ in 0..=definitions.len() {
        match definitions.get(&value)? {
            // A `ptrtoptr ptr to Func(sig)` is a re-spelled `ptr -> Func`
            // reification ([`call_through_code_addresses`]), followed as that
            // reification was.
            Inst::Copy { operand, .. }
            | Inst::Cast {
                op: CastOp::ReifyFnPointer,
                operand,
                ..
            }
            | Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Func(_),
                operand,
            } => value = *operand,
            Inst::Const {
                ty: Ty::Func(declared),
                value: Constant::FnDef(callee),
            } => return Some((*callee, *declared)),
            _ => return None,
        }
    }
    None
}

/// An indirect call through a function ITEM names that item's OWN signature id.
///
/// The lane interns a function-pointer signature per use, so the `FnDef`
/// constant (typed with its callee's declared `FuncTyId`) and the indirect call
/// that calls it (typed with the pointer type's freshly interned `FuncTyId`) can
/// name two entries of the module's `func_types` that are EQUAL. trust-ir
/// compares the ids, not the entries: where the callee's provenance is visible
/// it requires the call's signature to be the `FnDef`'s declared one
/// (`CallEdgeSignatureMismatch`), so a validating ingestion entry (WS7.3)
/// refused, for example, `-Copt-level=2` code calling a `fn(*mut u32) -> &mut u32`
/// item through a pointer. Where the constant's declared id is the callee's own
/// `ty` and the two entries are equal, the call takes that id: the same
/// signature, so nothing the call passes or returns changes. Any other
/// disagreement (a different signature, a constant typed with another id than
/// its callee's, provenance through a block parameter) is left as it was, for
/// the validator to report.
fn call_fn_items_at_their_own_signature(func: &mut Function, module: &Module) {
    let mut retyped: Vec<(usize, usize, FuncTyId)> = Vec::new();
    {
        let mut definitions: HashMap<ValueId, &Inst> = HashMap::new();
        for block in &func.blocks {
            for node in &block.body {
                if let [result] = node.results.as_slice() {
                    definitions.insert(*result, &node.inst);
                }
            }
        }
        for (block_index, block) in func.blocks.iter().enumerate() {
            for (node_index, node) in block.body.iter().enumerate() {
                let (Inst::CallIndirect { callee, sig, .. }
                | Inst::CallIndirectCannotUnwind { callee, sig, .. }
                | Inst::InvokeIndirect { callee, sig, .. }) = &node.inst
                else {
                    continue;
                };
                let Some((item, declared)) = fn_item_callee(&definitions, *callee) else {
                    continue;
                };
                if declared == *sig {
                    continue;
                }
                let item_ty = if item == func.id {
                    Some(func.ty)
                } else {
                    module
                        .functions
                        .iter()
                        .find(|candidate| candidate.id == item)
                        .map(|candidate| candidate.ty)
                };
                if item_ty != Some(declared) {
                    continue;
                }
                match (module.func_type(declared), module.func_type(*sig)) {
                    (Some(want), Some(have)) if want == have => {
                        retyped.push((block_index, node_index, declared));
                    }
                    _ => {}
                }
            }
        }
    }
    for (block_index, node_index, declared) in retyped {
        if let Inst::CallIndirect { sig, .. }
        | Inst::CallIndirectCannotUnwind { sig, .. }
        | Inst::InvokeIndirect { sig, .. } = &mut func.blocks[block_index].body[node_index].inst
        {
            *sig = declared;
        }
    }
}

/// The callee operand and signature of an indirect call.
fn indirect_callee_mut(inst: &mut Inst) -> Option<(&mut ValueId, FuncTyId)> {
    match inst {
        Inst::CallIndirect { callee, sig, .. }
        | Inst::CallIndirectCannotUnwind { callee, sig, .. }
        | Inst::InvokeIndirect { callee, sig, .. } => Some((callee, *sig)),
        _ => None,
    }
}

/// A runtime code address (a `fn(..)` pointer value, a vtable method slot, a
/// drop-glue slot) is called THROUGH the address: trust-ir's indirect call takes
/// a pointer-like callee (as the adapter does: `Func`, `Ptr` or a 64-bit code
/// address). The lane instead re-typed the address with
/// `cast reify_fn_pointer ptr to Func(sig)`, which trust-ir defines only from a
/// function ITEM (`CastLayoutUnsupported: reify_fn_pointer source must be a
/// function item`). Where such a cast's result is used ONLY as the callee of
/// indirect calls of the same signature, each of those calls takes the address
/// itself and the cast is dropped: the same register is called, and the
/// signature still names the call.
///
/// A cast with any other use — the code address handed to the typed
/// `indirect_unwind` forwarding thunk, whose first parameter is the `Func(sig)`
/// it calls, is the measured one — still needs a `Func(sig)` VALUE. It is
/// re-spelled as `ptrtoptr ptr to Func(sig)` (LD-50): trust-ir defines that
/// re-type between two one-word thin pointer layouts, and the adapter lowers it
/// to the same register move the reification was. It asserts no more than the
/// reification did: the lane emits this cast only where Rust's type system
/// already makes the address a code pointer of `sig` (a `fn(..)` value, a vtable
/// method or drop-glue slot); the re-spelling adds no new producer of it.
fn call_through_code_addresses(func: &mut Function) {
    call_through_code_addresses_of_callees(func);
    for block in &mut func.blocks {
        for node in &mut block.body {
            if let Inst::Cast {
                op: op @ CastOp::ReifyFnPointer,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Func(_),
                ..
            } = &mut node.inst
            {
                *op = CastOp::PtrToPtr;
            }
        }
    }
}

/// The callee-only half of [`call_through_code_addresses`].
fn call_through_code_addresses_of_callees(func: &mut Function) {
    let mut reified: HashMap<ValueId, (ValueId, FuncTyId)> = HashMap::new();
    for block in &func.blocks {
        for node in &block.body {
            if let (
                Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    src_ty: Ty::Ptr,
                    dst_ty: Ty::Func(sig),
                    operand,
                },
                [result],
            ) = (&node.inst, node.results.as_slice())
            {
                reified.insert(*result, (*operand, *sig));
            }
        }
    }
    if reified.is_empty() {
        return;
    }
    // Every use of a reified value, and the uses that are a same-signature
    // indirect callee.
    let mut uses: HashMap<ValueId, (usize, usize)> = HashMap::new();
    for block in &mut func.blocks {
        for node in &mut block.body {
            node.inst.visit_value_operands(|value| {
                if reified.contains_key(&value) {
                    uses.entry(value).or_default().0 += 1;
                }
            });
            if let Some((callee, sig)) = indirect_callee_mut(&mut node.inst) {
                if reified
                    .get(callee)
                    .is_some_and(|(_, reified_sig)| *reified_sig == sig)
                {
                    uses.entry(*callee).or_default().1 += 1;
                }
            }
        }
    }
    let rewritten: HashMap<ValueId, ValueId> = reified
        .into_iter()
        .filter(|(result, _)| uses.get(result).is_some_and(|(all, calls)| all == calls))
        .map(|(result, (operand, _))| (result, operand))
        .collect();
    if rewritten.is_empty() {
        return;
    }
    for block in &mut func.blocks {
        block.body.retain(|node| {
            !(matches!(
                node.inst,
                Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    ..
                }
            ) && node.results.len() == 1
                && rewritten.contains_key(&node.results[0]))
        });
        for node in &mut block.body {
            if let Some((callee, _)) = indirect_callee_mut(&mut node.inst) {
                if let Some(address) = rewritten.get(callee) {
                    *callee = *address;
                }
            }
        }
    }
}

/// An entry parameter declared with one thin-pointer type in the signature and
/// another in the entry block takes the signature's type; its old value is
/// re-defined by a `PtrToPtr` to the old type at the top of the entry block.
fn legalize_entry_params(
    func: &mut Function,
    module: &Module,
    fresh: &mut impl FnMut() -> ValueId,
) {
    let Some(sig) = module.func_type(func.ty) else {
        return;
    };
    let entry = func.entry;
    let Some(block) = func.blocks.iter_mut().find(|block| block.id == entry) else {
        return;
    };
    if block.params.len() != sig.params.len() {
        return;
    }
    let mut prologue = Vec::new();
    for ((value, ty), declared) in block.params.iter_mut().zip(&sig.params) {
        if ty == declared || !can_retype_thin_address(declared, ty) {
            continue;
        }
        let incoming = fresh();
        prologue.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: declared.clone(),
                dst_ty: ty.clone(),
                operand: incoming,
            })
            .with_result(*value),
        );
        *value = incoming;
        *ty = declared.clone();
    }
    if !prologue.is_empty() {
        prologue.append(&mut block.body);
        block.body = prologue;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{Block, BlockId, FuncId, FuncTy, TyId};

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    fn lane_pair() -> Ty {
        Ty::Array(TyId::new(3), 2)
    }

    /// A module with `callee(<param>) -> ()` (function 1) and the function
    /// under test (function 0, `caller_sig`).
    fn module_with(param: Ty, caller_sig: FuncTy) -> Module {
        let mut module = Module::new("abi-edges");
        module.func_types.push(caller_sig);
        module.func_types.push(FuncTy {
            params: vec![param],
            returns: vec![],
            is_vararg: false,
            abi: None,
        });
        let mut callee = Function::new(FuncId::new(1), "callee", FuncTyId::new(1), BlockId::new(0));
        callee.blocks.clear();
        module.functions.push(callee);
        module
    }

    fn caller(body: Vec<InstrNode>, params: Vec<(ValueId, Ty)>) -> Function {
        let mut func = Function::new(FuncId::new(0), "caller", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params = params;
        block.body = body;
        func.blocks = vec![block];
        func
    }

    fn void_sig(params: Vec<Ty>) -> FuncTy {
        FuncTy {
            params,
            returns: vec![],
            is_vararg: false,
            abi: None,
        }
    }

    fn counter(start: u32) -> impl FnMut() -> ValueId {
        let mut next = start;
        move || {
            let value = ValueId::new(next);
            next += 1;
            value
        }
    }

    #[test]
    fn slot_address_argument_is_loaded_as_the_declared_aggregate() {
        let module = module_with(lane_pair(), void_sig(vec![]));
        let mut func = caller(
            vec![
                InstrNode::new(Inst::Alloca {
                    ty: lane_pair(),
                    count: None,
                    align: None,
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![v(1)],
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
            vec![],
        );
        legalize_abi_edges(&mut func, &module, counter(10));
        let body = &func.blocks[0].body;
        assert_eq!(body.len(), 4);
        assert_eq!(
            body[1].inst,
            Inst::Load {
                ty: lane_pair(),
                ptr: v(1),
                volatile: false,
                align: None,
            }
        );
        assert_eq!(body[1].results, vec![v(10)]);
        assert_eq!(
            body[2].inst,
            Inst::Call {
                callee: FuncId::new(1),
                args: vec![v(10)],
            }
        );
    }

    #[test]
    fn plain_address_argument_is_retyped_to_the_declared_reference() {
        let reference = Ty::Ref(Box::new(lane_pair()));
        let module = module_with(reference.clone(), void_sig(vec![Ty::Ptr]));
        let mut func = caller(
            vec![
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![v(1)],
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
            vec![(v(1), Ty::Ptr)],
        );
        legalize_abi_edges(&mut func, &module, counter(10));
        let body = &func.blocks[0].body;
        assert_eq!(
            body[0].inst,
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: reference,
                operand: v(1),
            }
        );
        assert_eq!(
            body[1].inst,
            Inst::Call {
                callee: FuncId::new(1),
                args: vec![v(10)],
            }
        );
    }

    #[test]
    fn slot_address_return_is_loaded_as_the_declared_aggregate() {
        let module = module_with(
            Ty::I64,
            FuncTy {
                params: vec![],
                returns: vec![lane_pair()],
                is_vararg: false,
                abi: None,
            },
        );
        let mut func = caller(
            vec![
                InstrNode::new(Inst::Alloca {
                    ty: lane_pair(),
                    count: None,
                    align: None,
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
            vec![],
        );
        legalize_abi_edges(&mut func, &module, counter(10));
        let body = &func.blocks[0].body;
        assert!(matches!(body[1].inst, Inst::Load { ptr, .. } if ptr == v(1)));
        assert_eq!(
            body[2].inst,
            Inst::Return {
                values: vec![v(10)]
            }
        );
    }

    #[test]
    fn entry_parameter_takes_the_declared_reference_type() {
        let reference = Ty::Ref(Box::new(lane_pair()));
        let module = module_with(Ty::I64, void_sig(vec![Ty::I64, reference.clone()]));
        let mut func = caller(
            vec![InstrNode::new(Inst::Return { values: vec![] })],
            vec![(v(1), Ty::I64), (v(2), Ty::Ptr)],
        );
        legalize_abi_edges(&mut func, &module, counter(10));
        let block = &func.blocks[0];
        assert_eq!(
            block.params,
            vec![(v(1), Ty::I64), (v(10), reference.clone())]
        );
        assert_eq!(
            block.body[0].inst,
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: reference,
                dst_ty: Ty::Ptr,
                operand: v(10),
            }
        );
        assert_eq!(block.body[0].results, vec![v(2)]);
    }

    /// A runtime code address re-typed only to be called is called through
    /// directly; one with another use keeps its cast.
    #[test]
    fn reified_code_address_is_called_through() {
        let module = module_with(Ty::I64, void_sig(vec![Ty::Ptr]));
        let reify = InstrNode::new(Inst::Cast {
            op: CastOp::ReifyFnPointer,
            src_ty: Ty::Ptr,
            dst_ty: Ty::Func(FuncTyId::new(1)),
            operand: v(1),
        })
        .with_result(v(2));
        let call = |callee| {
            InstrNode::new(Inst::CallIndirect {
                callee,
                sig: FuncTyId::new(1),
                args: vec![v(3)],
                calling_conv: trust_ir::CallingConv::default(),
            })
        };
        let three = InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: trust_ir::Constant::Int(3),
        })
        .with_result(v(3));
        let ret = InstrNode::new(Inst::Return { values: vec![] });
        let mut func = caller(
            vec![three.clone(), reify.clone(), call(v(2)), ret.clone()],
            vec![(v(1), Ty::Ptr)],
        );
        legalize_abi_edges(&mut func, &module, counter(10));
        assert_eq!(
            func.blocks[0].body,
            vec![three.clone(), call(v(1)), ret.clone()]
        );

        // A second, non-call use keeps the call and a cast to the `Func(sig)`
        // value, re-spelled as the `ptrtoptr` re-type trust-ir defines (LD-50).
        let keep = InstrNode::new(Inst::Copy {
            ty: Ty::Func(FuncTyId::new(1)),
            operand: v(2),
        })
        .with_result(v(4));
        let retyped = InstrNode::new(Inst::Cast {
            op: CastOp::PtrToPtr,
            src_ty: Ty::Ptr,
            dst_ty: Ty::Func(FuncTyId::new(1)),
            operand: v(1),
        })
        .with_result(v(2));
        let original = vec![three.clone(), reify, call(v(2)), keep.clone(), ret.clone()];
        let mut func = caller(original, vec![(v(1), Ty::Ptr)]);
        legalize_abi_edges(&mut func, &module, counter(10));
        assert_eq!(
            func.blocks[0].body,
            vec![three, retyped, call(v(2)), keep, ret]
        );
    }

    /// An indirect call through a reified function ITEM takes the item's own
    /// signature id when the call's id names an equal entry; a call whose
    /// signature differs keeps it, for the validator to report.
    #[test]
    fn fn_item_called_indirectly_takes_its_own_signature_id() {
        let build = |copy_param: Ty| {
            let mut module = module_with(Ty::I64, void_sig(vec![]));
            module.func_types.push(void_sig(vec![copy_param]));
            module
        };
        let body = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Func(FuncTyId::new(1)),
                value: Constant::FnDef(FuncId::new(1)),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Cast {
                op: CastOp::ReifyFnPointer,
                src_ty: Ty::Func(FuncTyId::new(1)),
                dst_ty: Ty::Ptr,
                operand: v(1),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Copy {
                ty: Ty::Ptr,
                operand: v(2),
            })
            .with_result(v(3)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(3),
            })
            .with_result(v(4)),
            InstrNode::new(Inst::CallIndirect {
                callee: v(3),
                sig: FuncTyId::new(2),
                args: vec![v(4)],
                calling_conv: trust_ir::CallingConv::default(),
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ];
        let sig_of = |func: &Function| match &func.blocks[0].body[4].inst {
            Inst::CallIndirect { sig, .. } => *sig,
            other => panic!("expected the indirect call, got {other:?}"),
        };
        // An equal entry under another id: the call names the item's own id.
        let module = build(Ty::I64);
        let mut func = caller(body.clone(), vec![]);
        legalize_abi_edges(&mut func, &module, counter(10));
        assert_eq!(sig_of(&func), FuncTyId::new(1));
        assert_eq!(
            func.blocks[0].body.len(),
            body.len(),
            "nothing else changes"
        );
        // A different signature: left for the validator.
        let module = build(Ty::I32);
        let mut func = caller(body.clone(), vec![]);
        legalize_abi_edges(&mut func, &module, counter(10));
        assert_eq!(sig_of(&func), FuncTyId::new(2));

        // The lane's own spelling at -O2: the item's address re-typed back to
        // the call's signature (`reify_fn_pointer ptr -> Func(2)`) and called
        // through. The code-address pass calls the address itself, and the
        // call then names the item's own signature.
        let module = build(Ty::I64);
        let mut retyped = body.clone();
        retyped.insert(
            4,
            InstrNode::new(Inst::Cast {
                op: CastOp::ReifyFnPointer,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Func(FuncTyId::new(2)),
                operand: v(3),
            })
            .with_result(v(5)),
        );
        if let Inst::CallIndirect { callee, .. } = &mut retyped[5].inst {
            *callee = v(5);
        }
        let mut func = caller(retyped, vec![]);
        legalize_abi_edges(&mut func, &module, counter(10));
        assert_eq!(
            func.blocks[0].body.len(),
            body.len(),
            "the re-typing cast is gone"
        );
        match &func.blocks[0].body[4].inst {
            Inst::CallIndirect { callee, sig, .. } => {
                assert_eq!((*callee, *sig), (v(3), FuncTyId::new(1)));
            }
            other => panic!("expected the indirect call, got {other:?}"),
        }
    }

    /// An unreachable `unreachable` stub is removed; an unreachable block with
    /// content, and a reachable stub, stay.
    #[test]
    fn unreachable_stubs_are_removed() {
        let mut func = caller(
            vec![InstrNode::new(Inst::Br {
                target: BlockId::new(1),
                args: vec![],
            })],
            vec![],
        );
        let stub = |id: u32| {
            let mut block = Block::new(BlockId::new(id));
            block.body.push(InstrNode::new(Inst::Unreachable));
            block
        };
        let mut live = stub(1);
        live.body = vec![InstrNode::new(Inst::Unreachable)];
        let mut dead_with_code = Block::new(BlockId::new(3));
        dead_with_code.body = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: trust_ir::Constant::Int(1),
            })
            .with_result(v(9)),
            InstrNode::new(Inst::Unreachable),
        ];
        func.blocks.extend([live, stub(2), dead_with_code]);
        drop_unreachable_stubs(&mut func);
        let ids: Vec<u32> = func.blocks.iter().map(|b| b.id.index()).collect();
        assert_eq!(ids, vec![0, 1, 3]);
    }

    /// Fail closed: a mismatch outside the two rules (an integer where an
    /// aggregate is declared, an aggregate where an address is) is left as it
    /// was, for the validator to report.
    #[test]
    fn other_mismatches_are_left_for_the_validator() {
        let module = module_with(lane_pair(), void_sig(vec![Ty::I64]));
        let original = vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![v(1)],
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ];
        let mut func = caller(original.clone(), vec![(v(1), Ty::I64)]);
        legalize_abi_edges(&mut func, &module, counter(10));
        assert_eq!(func.blocks[0].body, original);

        let module = module_with(Ty::Ptr, void_sig(vec![lane_pair()]));
        let mut func = caller(original.clone(), vec![(v(1), lane_pair())]);
        legalize_abi_edges(&mut func, &module, counter(10));
        assert_eq!(func.blocks[0].body, original);
    }
}
