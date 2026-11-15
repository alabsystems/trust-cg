// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Real-body routing for aggregate-valued iterator maps.
//!
//! The scalar iterator drive is not a generic value representation. A Map
//! returning an already-supported aggregate must retain its actual closure
//! return ABI and std constructor/consumer bodies, or refuse in that ordinary
//! lowering. This classifier grants no module or proof admission.

use super::*;

/// The real core Map whose actual closure returns a fixed scalar-leaf
/// aggregate already admitted by the ordinary aggregate/Vec image machinery,
/// or whose closure's captures hold such a closure
/// ([`iterator_callback_takes_real_body`]). Other scalar maps keep their fast
/// drive; pointer, droppable, wide-leaf and other unqualified image outputs
/// keep their existing refusal.
pub(super) fn map_requires_real_body<'tcx>(tcx: TyCtxt<'tcx>, iterator: Ty<'tcx>) -> bool {
    let ty::Adt(adt, args) = iterator.kind() else {
        return false;
    };
    if adapter_kind_of(tcx, adt.did()) != Some(AdapterTag::Map) || args.len() < 2 {
        return false;
    }
    iterator_callback_takes_real_body(tcx, args.type_at(1))
}

/// Whether a callback that the bridge calls through its own body must instead
/// be left to std's ordinary body: an actual closure whose own output needs the
/// existing aggregate image ABI, or a real std closure holding such a closure
/// among its captures. Std's Map glue (`map_fold`, `map_try_fold`) captures the
/// mapper after forwarding to the bare inner iterator, and further std glue
/// (`for_each::call`, `extend_trusted`'s writer) captures that glue: the
/// receiver no longer contains Map, but these captures keep the original typed
/// custody.
///
/// Captures are followed only through closures defined in the real core, alloc
/// or std crate (identity, not a crate-name string). A model hand-calls any
/// other closure through its own body (`emit_closure_call_n`), which lowers each
/// call of a captured closure as an ordinary MIR closure call with that
/// callee's own return ABI, so only that closure's own output decides. Only
/// the in-place `Vec` models ([`VEC_CALLBACK_MODELS`]) decide their closure
/// argument by this predicate ([`vec_call_argument_takes_real_body`]).
/// References and tuples among std captures are followed; unrelated ADTs and
/// callable lookalike names are not closure evidence. This only retains
/// ordinary bodies.
pub(super) fn callback_requires_real_body<'tcx>(tcx: TyCtxt<'tcx>, callback: Ty<'tcx>) -> bool {
    aggregate_output_in_custody(tcx, callback, false)
}

/// The iterator drives' decision: [`callback_requires_real_body`], or any
/// callback whose captures (followed through every closure, not only std
/// glue) hold a closure with an admitted aggregate output.
///
/// The second arm is a route, not a correctness requirement: a drive calls a
/// user callback through its own body exactly as the in-place `Vec` models
/// do. It is kept because the real bodies it selects lower and match LLVM
/// where the drives refuse every capturing callback of the same shape
/// (`try_fold` breaking with an `Option`, a Map `for_each` and
/// `extend_trusted` at `-O2`/`-O3`, a fold over `.map(f).enumerate()` at
/// `-O0`/`-O1`); measured, withdrawing it turns those matches into refusals
/// (OD-CAPTURED-PAIR-CALLBACK-20261009). The receiver decision (`real_body_iterator_receiver`)
/// and the dead-body exclusion (`ty_mentions_real_body_iterator_source`) use
/// this one predicate, so a body this route reaches is never trapped as dead.
/// `lower_vec_call` uses it too, for every callee outside
/// [`VEC_CALLBACK_MODELS`] ([`vec_call_argument_takes_real_body`]).
pub(super) fn iterator_callback_takes_real_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    callback: Ty<'tcx>,
) -> bool {
    aggregate_output_in_custody(tcx, callback, true)
}

/// The `Vec` methods whose model arm in `lower_vec_call` calls a closure
/// argument through that closure's own body: `retain` and `retain_mut`
/// (`lower_vec_retain`), `dedup_by` (`lower_vec_dedup_by`) and `resize_with`
/// (`lower_vec_resize_with`). It names exactly those arms. A name here
/// without such an arm would send the closures the iterator route keeps on
/// std's body to the by-name refusal instead; an arm missing here would send
/// a closure that only calls a captured aggregate-returning closure to std's
/// body (for `resize_with`, `extend_trusted`, refused by name). Neither
/// mismatch admits a closure whose own output is an admitted aggregate: both
/// predicates leave that to std's body.
pub(super) const VEC_CALLBACK_MODELS: [&str; 4] =
    ["retain", "retain_mut", "dedup_by", "resize_with"];

/// `lower_vec_call`'s decision for one actual argument of the std callee
/// `name` (a modeled `Vec<element>` self or destination), taken before any
/// slot, binding, allocation or callback: whether the call keeps std's
/// ordinary body. An argument holding a Map with an admitted aggregate output
/// always does ([`mentions_aggregate_map`]). An argument a model arm calls
/// ([`vec_model_calls_argument`]) is judged by [`callback_requires_real_body`]:
/// the model calls that closure's body, which calls any captured closure with
/// that closure's own return ABI. Every other argument keeps
/// [`iterator_callback_takes_real_body`]: past this decision its call is
/// declined (`dedup_by_key`), refused by name (`pop_if`, `extract_if` and the
/// `ExtractIf` constructor it inlines to at `-O2`/`-O3`,
/// `Option`/`Result::map_or[_else]` producing a `Vec`), or reaches a model
/// arm that refuses it by name (a `&F`/`&mut F` payload, an element the arm
/// does not move). For those, a closure capturing an aggregate-returning
/// closure keeps std's body, which matches LLVM; the narrower walk refused
/// them by name (OD-CAPTURED-PAIR-CALLBACK-20261009). Their scalar-capturing
/// counterparts are refused by name under either walk: like the iterator
/// drives' capture arm, this is a capability route, not a correctness rule.
pub(super) fn vec_call_argument_takes_real_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: &str,
    element: Ty<'tcx>,
    argument: Ty<'tcx>,
) -> bool {
    mentions_aggregate_map(tcx, argument)
        || if vec_model_calls_argument(tcx, name, element, argument) {
            callback_requires_real_body(tcx, argument)
        } else {
            iterator_callback_takes_real_body(tcx, argument)
        }
}

/// Whether `name`'s model arm calls `argument` through its own body rather
/// than refusing the call by name: a [`VEC_CALLBACK_MODELS`] method, a
/// by-value closure (each arm refuses a `&F` or `&mut F` payload), and an
/// element the arms move (a single scalar of 1, 2, 4 or 8 bytes, or a
/// struct-class element `vec_struct_element_admissible` admits; each arm
/// refuses any other, such as `u128` or `Option<u64>`). This mirrors the
/// arms' own leading checks; a drift either way only moves a call between
/// std's body and a by-name refusal.
fn vec_model_calls_argument<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: &str,
    element: Ty<'tcx>,
    argument: Ty<'tcx>,
) -> bool {
    VEC_CALLBACK_MODELS.contains(&name)
        && matches!(argument.kind(), ty::Closure(..))
        && if rust_ty_to_trust_ir_ty(tcx, element).is_ok() {
            matches!(
                element_layout_size_align(tcx, element),
                Ok((1 | 2 | 4 | 8, _))
            )
        } else {
            vec_struct_element_admissible(tcx, element)
        }
}

/// The shared walk: `callback` (references peeled) is a closure whose own
/// output is admitted, or one of its captures is, followed through references,
/// tuples and closures: every closure when `through_any_closure`, otherwise
/// only real std closures.
fn aggregate_output_in_custody<'tcx>(
    tcx: TyCtxt<'tcx>,
    callback: Ty<'tcx>,
    through_any_closure: bool,
) -> bool {
    let follows = |definition: DefId| through_any_closure || is_real_std_crate_def(tcx, definition);
    let mut callback = callback;
    while let ty::Ref(_, inner, _) = callback.kind() {
        callback = *inner;
    }
    let ty::Closure(definition, closure_args) = callback.kind() else {
        return false;
    };
    let signature = tcx.instantiate_bound_regions_with_erased(closure_args.as_closure().sig());
    if output_requires_real_body(tcx, signature.output()) {
        return true;
    }
    if !follows(*definition) {
        return false;
    }
    let captures = closure_args.as_closure().upvar_tys();
    if captures.is_empty() {
        return false;
    }
    // The ordinary non-capturing case allocates no traversal scratch.
    let mut pending: Vec<_> = captures.iter().collect();
    let mut seen = HashSet::new();
    while let Some(capture) = pending.pop() {
        if !seen.insert(capture) {
            continue;
        }
        match capture.kind() {
            ty::Ref(_, inner, _) => pending.push(*inner),
            ty::Tuple(fields) => pending.extend(fields.iter()),
            ty::Closure(definition, closure_args) => {
                let signature =
                    tcx.instantiate_bound_regions_with_erased(closure_args.as_closure().sig());
                if output_requires_real_body(tcx, signature.output()) {
                    return true;
                }
                if follows(*definition) {
                    pending.extend(closure_args.as_closure().upvar_tys().iter());
                }
            }
            _ => {}
        }
    }
    false
}

fn output_requires_real_body<'tcx>(tcx: TyCtxt<'tcx>, output: Ty<'tcx>) -> bool {
    let output = tcx.normalize_erasing_regions(
        ty::TypingEnv::fully_monomorphized(),
        ty::Unnormalized::new(output),
    );
    // The sole output eligibility rule: same bounded image, scalar
    // disjointness, pointer/drop/wide refusals as Vec.
    vec_struct_element_admissible(tcx, output)
}

/// Used both before chain resolution and by the existing live-body protection
/// on std instance types. Keeping one decision closes the reachable-stub seam
/// when adapters or standard helper generics wrap the aggregate-valued Map.
pub(super) fn mentions_aggregate_map<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    ty.walk().any(|argument| {
        argument
            .as_type()
            .is_some_and(|ty| map_requires_real_body(tcx, ty))
    })
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod callback_tests;
