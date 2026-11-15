// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

include!(concat!(env!("OUT_DIR"), "/test_build_compiler.rs"));

const PROBE: &str = r#"
pub struct Pair { pub value: u32, pub index: usize }
pub struct Map<I, F> { pub iterator: I, pub callback: F }
#[inline(never)] fn observe<T>(_: &T) {}
pub fn cached_index_collect(xs: &[usize]) -> Vec<(usize, usize)> {
    xs.iter().map(|x| *x).enumerate().map(|(i, key)| (key, i)).collect()
}
pub fn tuple_collect(xs: &[u32]) -> Vec<(u32, usize)> {
    xs.iter().map(|x| (*x, 7usize)).collect()
}
pub fn struct_collect(xs: &[u32]) -> Vec<Pair> {
    xs.iter().map(|x| Pair { value: *x, index: 7 }).collect()
}
pub fn captured_callback() {
    let mapper = |x: u32| (x, 7usize);
    let callback = move |x: u32| mapper(x).0;
    observe(&callback);
}
pub fn scalar_callback() { let f = |x: u32| x + 1; observe(&f); }
pub fn pointer_callback(xs: &[u32]) {
    let f = |x: u32| (xs.as_ptr(), x); observe(&f);
}
pub fn wide_callback() { let f = |x: u32| (x as u128, x); observe(&f); }
pub fn drop_callback() { let f = |x: u32| (Box::new(x), x); observe(&f); }
pub fn fake_map(xs: &[u32]) {
    let it = Map { iterator: xs.iter(), callback: |x: &u32| (*x, 7usize) };
    observe(&it);
}
pub fn captured_try_fold(xs: &[u32]) -> Result<u32, ()> {
    let mapper = |x: u32| (x, 7usize);
    xs.iter().try_fold(0, move |acc, x| Ok(acc + mapper(*x).0))
}
pub fn captured_scalar_collect(xs: &[u32]) -> Vec<u32> {
    let mapper = |x: u32| (x, 7usize);
    xs.iter().map(move |x| mapper(*x).0 + 1).collect()
}
pub fn captured_scalar_rev_fold(xs: &[u32]) -> u32 {
    let mapper = |x: u32| (x, 7usize);
    xs.iter().rev().map(move |x| mapper(*x).0).fold(0, |a, y| a * 3 + y)
}
pub fn glue_try_fold(xs: &[u32]) -> Result<u32, ()> {
    xs.iter().map(|x| (*x, 7usize)).try_fold(0, |acc, (a, _)| Ok(acc + a))
}
pub fn captured_pop_if(v: &mut Vec<u64>) -> Option<u64> {
    let mk = |x: u64| (x, x * 9);
    v.pop_if(|x| { let (a, b) = mk(*x); a + b > 20 })
}
pub fn captured_map_or_else(o: Option<u64>) -> Vec<u64> {
    let mk = |x: u64| (x, x * 9);
    o.map_or_else(Vec::new, |x| { let (a, b) = mk(x); vec![a, b] })
}
pub fn captured_resize_with(v: &mut Vec<u64>) {
    let mk = |x: u64| (x, x * 9);
    let mut k = 0u64;
    v.resize_with(5, || { k += 1; let (a, b) = mk(k); a + b });
}
pub fn captured_retain(v: &mut Vec<u64>) {
    let mk = |x: u64| (x, x * 9);
    v.retain(|x| { let (a, b) = mk(*x); a + b > 20 });
}
pub fn captured_retain_by_ref(v: &mut Vec<u64>) {
    let mk = |x: u64| (x, x * 9);
    let mut f = |x: &u64| { let (a, b) = mk(*x); a + b > 20 };
    v.retain(&mut f);
}
pub fn captured_retain_u128(v: &mut Vec<u128>) {
    let mk = |x: u64| (x, x * 9);
    v.retain(|x| { let (a, b) = mk(*x as u64); a + b > 20 });
}
pub fn captured_dedup_by_option(v: &mut Vec<Option<u64>>) {
    let mk = |x: u64| (x, x * 9);
    v.dedup_by(|a, b| { let (p, _) = mk(a.unwrap_or(0)); let (q, _) = mk(b.unwrap_or(0)); p == q });
}
pub fn own_pair_resize_with(v: &mut Vec<(u64, u64)>) {
    let mut k = 0u64;
    v.resize_with(5, || { k += 1; (k, k * 9) });
}
trait FakeFold: Sized {
    fn fold<F: FnMut(u32) -> (u32, usize)>(self, _f: F) -> u32 { 41 }
}
impl FakeFold for u32 {}
pub fn fake_fold() -> u32 { FakeFold::fold(3, |x| (x, 7)) }
"#;

fn call_view<'a, 'tcx>(terminator: &'a mir::Terminator<'tcx>) -> DirectCallTerminator<'a, 'tcx> {
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        unwind,
        fn_span,
        ..
    } = &terminator.kind
    else {
        panic!("actual MIR call required")
    };
    DirectCallTerminator {
        func,
        args,
        destination,
        target: *target,
        unwind,
        fn_span: *fn_span,
        source_info: terminator.source_info,
    }
}

fn state(ctx: &MirLoweringCtx<'_>) -> [usize; 10] {
    [
        ctx.next_value as usize,
        ctx.next_block_id as usize,
        ctx.extra_blocks.len(),
        ctx.module.functions.len(),
        ctx.module.func_types.len(),
        ctx.scalar_values.len(),
        ctx.vec_slot_addrs.len(),
        ctx.projected_values.len(),
        ctx.extern_callees.len(),
        ctx.memory_slots.len(),
    ]
}

fn assert_fallthrough<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    call: &DirectCallTerminator<'_, 'tcx>,
    callee: Instance<'tcx>,
    label: &str,
) {
    let before = state(ctx);
    let mut block = Block::new(BlockId::new(0));
    assert!(
        !lower_vec_call(ctx, body, &mut block, call, callee)
            .unwrap_or_else(|e| panic!("{label}: Vec path: {e}"))
    );
    assert!(
        !lower_iterator_call(ctx, body, &mut block, call, callee)
            .unwrap_or_else(|e| panic!("{label}: iterator path: {e}"))
    );
    let name = callee_item_name_str(ctx.tcx, callee.def_id());
    match name.as_str() {
        "fold" => assert!(
            !lower_iter_consumer(ctx, body, &mut block, call, "fold", false)
                .unwrap_or_else(|e| panic!("{label}: direct fold path: {e}"))
        ),
        "for_each" => assert!(
            !lower_iter_for_each(ctx, body, &mut block, call)
                .unwrap_or_else(|e| panic!("{label}: direct for_each path: {e}"))
        ),
        "try_fold" => assert!(
            !lower_iter_try_fold(ctx, body, &mut block, call, false)
                .unwrap_or_else(|e| panic!("{label}: direct try_fold path: {e}"))
        ),
        _ => {}
    }
    assert_eq!(
        state(ctx),
        before,
        "{label}: no synthetic bindings or ownership changes"
    );
    assert!(block.body.is_empty(), "{label}: no emitted scalar drive");
    assert!(block.params.is_empty(), "{label}: no synthetic parameters");
}

fn source<'tcx>(tcx: TyCtxt<'tcx>, name: &str) -> Instance<'tcx> {
    let definition = tcx
        .hir_body_owners()
        .find(|d| {
            matches!(tcx.def_kind(d.to_def_id()), rustc_hir::def::DefKind::Fn)
                && tcx.item_name(d.to_def_id()).as_str() == name
        })
        .unwrap_or_else(|| panic!("missing actual source {name}"));
    Instance::mono(tcx, definition.to_def_id())
}

fn check_callback_rows(tcx: TyCtxt<'_>) {
    // (row, iterator drives' decision, in-place Vec model decision)
    for (name, iterator_expected, model_expected) in [
        ("captured_callback", true, false),
        ("scalar_callback", false, false),
        ("pointer_callback", false, false),
        ("wide_callback", false, false),
        ("drop_callback", false, false),
    ] {
        let instance = source(tcx, name);
        let body = tcx.instance_mir(instance.def);
        let ctx = MirLoweringCtx::new("callback_rows", tcx, instance);
        let callbacks: Vec<_> = body
            .local_decls
            .iter()
            .map(|d| ctx.monomorphize_ty(d.ty))
            .filter(|t| matches!(t.kind(), ty::Closure(..)))
            .collect();
        assert!(!callbacks.is_empty(), "{name}: actual closure locals");
        assert_eq!(
            callbacks
                .iter()
                .any(|t| iterator_callback_takes_real_body(tcx, *t)),
            iterator_expected,
            "{name}: actual output/capture eligibility for the iterator drives"
        );
        assert_eq!(
            callbacks
                .iter()
                .any(|t| callback_requires_real_body(tcx, *t)),
            model_expected,
            "{name}: actual own-output eligibility for the in-place Vec models"
        );
        if name == "captured_callback" {
            let outer = callbacks
                .iter()
                .find(|t| {
                    let ty::Closure(_, args) = t.kind() else {
                        return false;
                    };
                    !args.as_closure().upvar_tys().is_empty()
                })
                .expect("actual outer closure with original mapper capture");
            let ty::Closure(definition, args) = outer.kind() else {
                panic!("actual closure")
            };
            assert!(!is_real_std_crate_def(tcx, *definition), "a user closure");
            let sig = tcx.instantiate_bound_regions_with_erased(args.as_closure().sig());
            assert_eq!(
                sig.output(),
                tcx.types.u32,
                "outer output is scalar, not a tuple"
            );
            // The iterator drives keep this callback's real-body route; a model
            // calls its body, which calls the captured pair mapper itself.
            assert!(iterator_callback_takes_real_body(tcx, *outer));
            assert!(!callback_requires_real_body(tcx, *outer));
        }
    }
    let instance = source(tcx, "fake_map");
    let body = tcx.instance_mir(instance.def);
    let fake = body
        .local_decls
        .iter()
        .map(|d| d.ty)
        .find(|t| {
            matches!(t.kind(), ty::Adt(adt, _) if adt.did().is_local()
            && tcx.item_name(adt.did()).as_str() == "Map")
        })
        .expect("actual user Map");
    assert!(!map_requires_real_body(tcx, fake));
    assert!(!mentions_aggregate_map(tcx, fake));
    assert!(
        !callback_requires_real_body(tcx, fake),
        "an ADT is not an actual callback"
    );
    let instance = source(tcx, "fake_fold");
    let body = tcx.instance_mir(instance.def);
    let mut ctx = MirLoweringCtx::new("fake_fold", tcx, instance);
    let mut checked = false;
    for data in body.basic_blocks.iter() {
        if !matches!(data.terminator().kind, TerminatorKind::Call { .. }) {
            continue;
        }
        let call = call_view(data.terminator());
        let callee = direct_callee_instance(&ctx, body, call.func, call.fn_span).unwrap();
        if callee_item_name_str(tcx, callee.def_id()) != "fold" {
            continue;
        }
        assert!(!is_real_std_crate_def(tcx, callee.def_id()));
        let before = state(&ctx);
        let mut block = Block::new(BlockId::new(0));
        assert!(!lower_iterator_call(&mut ctx, body, &mut block, &call, callee).unwrap());
        assert_eq!(state(&ctx), before);
        assert!(block.body.is_empty());
        checked = true;
    }
    assert!(checked, "actual local fake fold call checked");
}

fn check_actual_nested_collection(tcx: TyCtxt<'_>) {
    let roots = ["cached_index_collect", "tuple_collect", "struct_collect"];
    let mut pending = roots
        .into_iter()
        .map(|name| (name, source(tcx, name)))
        .collect::<Vec<_>>();
    let mut visited = HashSet::new();
    let mut stages = HashSet::new();
    let mut peeled_tuple_fold = false;
    let mut peeled_scalar_fold = false;
    while let Some((root, instance)) = pending.pop() {
        if !visited.insert((root, instance)) {
            continue;
        }
        assert!(visited.len() <= 160, "bounded actual std custody graph");
        let body = tcx.instance_mir(instance.def);
        let mut ctx = MirLoweringCtx::new("callback_graph", tcx, instance);
        for data in body.basic_blocks.iter() {
            if !matches!(data.terminator().kind, TerminatorKind::Call { .. }) {
                continue;
            }
            let call = call_view(data.terminator());
            let Ok(callee) = direct_callee_instance(&ctx, body, call.func, call.fn_span) else {
                continue; // Indirect calls have no std Instance to traverse.
            };
            if !is_real_std_crate_def(tcx, callee.def_id())
                || !std_def_is_interceptable(tcx, callee.def_id())
            {
                continue;
            }
            let mut map_arg = false;
            let mut callback_arg = false;
            for argument in call.args {
                let ty = ctx.monomorphize_ty(operand_rust_ty(&ctx, body, &argument.node).unwrap());
                map_arg |= mentions_aggregate_map(tcx, ty);
                let iterator_decision = iterator_callback_takes_real_body(tcx, ty);
                // Every callback on these paths is std glue or the mapper
                // itself: the model decision follows the same custody.
                assert_eq!(
                    callback_requires_real_body(tcx, ty),
                    iterator_decision,
                    "{root}: std glue custody of {ty:?}"
                );
                callback_arg |= iterator_decision;
            }
            if !map_arg && !callback_arg {
                continue;
            }
            let name = callee_item_name_str(tcx, callee.def_id());
            assert!(
                !is_dead_std_iterator_reduction_body(tcx, callee),
                "{root}/{name}: the actual std custody body must stay live"
            );
            if matches!(
                name.as_str(),
                "collect" | "spec_extend" | "extend_trusted" | "for_each" | "fold"
            ) {
                assert_fallthrough(&mut ctx, body, &call, callee, &format!("{root}/{name}"));
                stages.insert((root, name.clone()));
            }
            if name == "fold" && callback_arg {
                let receiver =
                    ctx.monomorphize_ty(operand_rust_ty(&ctx, body, &call.args[0].node).unwrap());
                if !mentions_aggregate_map(tcx, receiver) {
                    assert!(real_body_iterator_receiver(&ctx, body, &call).unwrap());
                    if let Some(chain) = resolve_iter_chain(&ctx, receiver).unwrap() {
                        if chain.item.tuple.is_some() {
                            peeled_tuple_fold = true;
                        } else {
                            peeled_scalar_fold = true;
                        }
                    }
                }
            }
            pending.push((root, callee));
        }
    }
    for root in roots {
        for stage in [
            "collect",
            "spec_extend",
            "extend_trusted",
            "for_each",
            "fold",
        ] {
            assert!(
                stages.contains(&(root, stage.to_owned())),
                "{root}: actual {stage} custody edge"
            );
        }
    }
    assert!(
        peeled_tuple_fold,
        "actual bare Enumerate fold retains aggregate mapper in callback"
    );
    assert!(
        peeled_scalar_fold,
        "further bare slice fold retains the same captured mapper"
    );
}

fn check_try_fold(tcx: TyCtxt<'_>) {
    let instance = source(tcx, "captured_try_fold");
    let body = tcx.instance_mir(instance.def);
    let mut ctx = MirLoweringCtx::new("callback_try_fold", tcx, instance);
    let mut checked = false;
    for data in body.basic_blocks.iter() {
        if !matches!(data.terminator().kind, TerminatorKind::Call { .. }) {
            continue;
        }
        let call = call_view(data.terminator());
        let callee = direct_callee_instance(&ctx, body, call.func, call.fn_span).unwrap();
        if callee_item_name_str(tcx, callee.def_id()) != "try_fold" {
            continue;
        }
        assert!(is_real_std_crate_def(tcx, callee.def_id()));
        let callback =
            ctx.monomorphize_ty(operand_rust_ty(&ctx, body, &call.args[2].node).unwrap());
        assert!(iterator_callback_takes_real_body(tcx, callback));
        assert!(
            !callback_requires_real_body(tcx, callback),
            "a user closure"
        );
        assert!(ty_mentions_real_body_iterator_source(tcx, callback));
        assert!(!is_dead_std_iterator_reduction_body(tcx, callee));
        assert_fallthrough(&mut ctx, body, &call, callee, "captured try_fold");
        checked = true;
    }
    assert!(
        checked,
        "actual typed try_fold consumer checked before any scalar emission"
    );
}

/// Every actual std call reachable from `root` through calls whose argument
/// types satisfy `follow`, with that call's monomorphic argument types.
fn std_calls_from<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: &str,
    follow: impl Fn(&[Ty<'tcx>]) -> bool,
    mut visit: impl FnMut(
        &MirLoweringCtx<'tcx>,
        &Body<'tcx>,
        &DirectCallTerminator<'_, 'tcx>,
        &str,
        &[Ty<'tcx>],
    ),
) {
    let mut pending = vec![source(tcx, root)];
    let mut visited = HashSet::new();
    while let Some(instance) = pending.pop() {
        if !visited.insert(instance) {
            continue;
        }
        assert!(
            visited.len() <= 160,
            "{root}: bounded actual std custody graph"
        );
        let body = tcx.instance_mir(instance.def);
        let ctx = MirLoweringCtx::new("callback_boundary", tcx, instance);
        for data in body.basic_blocks.iter() {
            if !matches!(data.terminator().kind, TerminatorKind::Call { .. }) {
                continue;
            }
            let call = call_view(data.terminator());
            let Ok(callee) = direct_callee_instance(&ctx, body, call.func, call.fn_span) else {
                continue; // Indirect calls have no std Instance to traverse.
            };
            if !is_real_std_crate_def(tcx, callee.def_id())
                || !std_def_is_interceptable(tcx, callee.def_id())
            {
                continue;
            }
            let arguments: Vec<_> = call
                .args
                .iter()
                .map(|a| ctx.monomorphize_ty(operand_rust_ty(&ctx, body, &a.node).unwrap()))
                .collect();
            if !follow(&arguments) {
                continue;
            }
            let name = callee_item_name_str(tcx, callee.def_id());
            visit(&ctx, body, &call, name.as_str(), &arguments);
            pending.push(callee);
        }
    }
}

/// Whether `ty` mentions a closure defined in the probe (a user closure)
/// anywhere among its component types, generic arguments included.
fn mentions_user_closure(ty: Ty<'_>) -> bool {
    ty.walk().any(|a| {
        a.as_type()
            .is_some_and(|t| matches!(t.kind(), ty::Closure(d, _) if d.is_local()))
    })
}

/// Whether the captures of std closure `glue` hold a user closure, through
/// references, tuples and further std closures (not generic arguments).
fn captures_user_closure<'tcx>(tcx: TyCtxt<'tcx>, glue: Ty<'tcx>) -> bool {
    let ty::Closure(_, args) = glue.kind() else {
        return false;
    };
    let mut pending: Vec<_> = args.as_closure().upvar_tys().iter().collect();
    while let Some(capture) = pending.pop() {
        match capture.kind() {
            ty::Ref(_, inner, _) => pending.push(*inner),
            ty::Tuple(fields) => pending.extend(fields.iter()),
            ty::Closure(definition, _) if definition.is_local() => return true,
            ty::Closure(definition, args) if is_real_std_crate_def(tcx, *definition) => {
                pending.extend(args.as_closure().upvar_tys().iter())
            }
            _ => {}
        }
    }
    false
}

/// Along std's whole custody path of a scalar user mapper that captures a pair
/// mapper, the in-place model decision stays scalar, including at the std glue
/// closure that captures the user mapper once Map is peeled off the receiver,
/// while the iterator drives keep their real-body route there. Std glue
/// holding an aggregate-output mapper (`map_try_fold(&mut f, g)`, through a
/// reference) takes the real body under both decisions.
fn check_std_glue_capture_boundary(tcx: TyCtxt<'_>) {
    for root in ["captured_scalar_collect", "captured_scalar_rev_fold"] {
        let mut calls = 0usize;
        let mut glue_over_user = false;
        std_calls_from(
            tcx,
            root,
            |arguments| arguments.iter().any(|t| mentions_user_closure(*t)),
            |_, _, _, name, arguments| {
                calls += 1;
                for argument in arguments {
                    assert!(
                        !callback_requires_real_body(tcx, *argument),
                        "{root}/{name}: {argument:?} keeps the model decision"
                    );
                    if let ty::Closure(glue, _) = argument.kind() {
                        if is_real_std_crate_def(tcx, *glue)
                            && captures_user_closure(tcx, *argument)
                        {
                            assert!(
                                iterator_callback_takes_real_body(tcx, *argument),
                                "{root}/{name}: the iterator route follows the user capture"
                            );
                            glue_over_user = true;
                        }
                    }
                }
            },
        );
        assert!(calls > 0, "{root}: actual std custody calls visited");
        assert!(
            glue_over_user,
            "{root}: an actual std glue closure capturing the user mapper was checked"
        );
    }
    let mut glue_try_fold = false;
    std_calls_from(
        tcx,
        "glue_try_fold",
        |arguments| {
            arguments.iter().any(|t| {
                mentions_aggregate_map(tcx, *t) || iterator_callback_takes_real_body(tcx, *t)
            })
        },
        |ctx, body, call, name, arguments| {
            if name != "try_fold" || mentions_aggregate_map(tcx, arguments[0]) {
                return;
            }
            let glue = arguments[2];
            let ty::Closure(definition, args) = glue.kind() else {
                return;
            };
            assert!(is_real_std_crate_def(tcx, *definition));
            assert!(
                args.as_closure()
                    .upvar_tys()
                    .iter()
                    .any(|u| matches!(u.kind(), ty::Ref(..))),
                "std glue holds the mapper by reference"
            );
            assert!(callback_requires_real_body(tcx, glue));
            assert!(iterator_callback_takes_real_body(tcx, glue));
            assert!(real_body_iterator_receiver(ctx, body, call).unwrap());
            glue_try_fold = true;
        },
    );
    assert!(
        glue_try_fold,
        "actual bare try_fold receiver retains the aggregate mapper through std glue"
    );
}

/// `lower_vec_call`'s argument decision on actual calls whose closure captures
/// a pair mapper. A model arm that calls the closure (`resize_with`,
/// `retain`) keeps it: the model calls the closure's body. A `Vec`-self or
/// `Vec`-destination std callee with no such arm (`pop_if`, `map_or_else`),
/// and a model call whose arm refuses its payload (`&mut F`) or element
/// (`u128`, `Option<u64>`), keeps std's body, with no emission, where the
/// model decision alone would leave it to a by-name refusal. A closure whose
/// own output is the pair leaves the model.
fn check_vec_call_closure_decisions(tcx: TyCtxt<'_>) {
    // (probe, callee, whether the call keeps std's body)
    for (root, callee_name, real_body) in [
        ("captured_pop_if", "pop_if", true),
        ("captured_map_or_else", "map_or_else", true),
        ("captured_resize_with", "resize_with", false),
        ("captured_retain", "retain", false),
        ("captured_retain_by_ref", "retain", true),
        ("captured_retain_u128", "retain", true),
        ("captured_dedup_by_option", "dedup_by", true),
        ("own_pair_resize_with", "resize_with", true),
    ] {
        let instance = source(tcx, root);
        let body = tcx.instance_mir(instance.def);
        let mut ctx = MirLoweringCtx::new("vec_call_closure", tcx, instance);
        let mut checked = false;
        for data in body.basic_blocks.iter() {
            if !matches!(data.terminator().kind, TerminatorKind::Call { .. }) {
                continue;
            }
            let call = call_view(data.terminator());
            let Ok(callee) = direct_callee_instance(&ctx, body, call.func, call.fn_span) else {
                continue;
            };
            if callee_item_name_str(tcx, callee.def_id()) != callee_name {
                continue;
            }
            assert!(
                is_real_std_crate_def(tcx, callee.def_id()),
                "{root}: actual std {callee_name}"
            );
            let arguments: Vec<_> = call
                .args
                .iter()
                .map(|a| ctx.monomorphize_ty(operand_rust_ty(&ctx, body, &a.node).unwrap()))
                .collect();
            let closure = arguments
                .iter()
                .copied()
                .find(|t| matches!(t.peel_refs().kind(), ty::Closure(d, _) if d.is_local()))
                .unwrap_or_else(|| panic!("{root}: actual user closure argument"));
            // The `Vec` element `lower_vec_call` takes from a `&mut Vec<T>`
            // self; a callee with another self has no model arm, so any
            // element serves.
            let element = vec_element_ty(tcx, arguments[0].peel_refs()).unwrap_or(tcx.types.u64);
            // The drives' capture walk takes every row's closure; only the
            // model rows judge it by its own output.
            assert!(iterator_callback_takes_real_body(tcx, closure), "{root}");
            assert_eq!(
                arguments.iter().any(|t| vec_call_argument_takes_real_body(
                    tcx,
                    callee_name,
                    element,
                    *t
                )),
                real_body,
                "{root}: lower_vec_call's argument decision"
            );
            assert!(
                vec_call_argument_takes_real_body(tcx, "pop_if", element, closure),
                "{root}: a callee with no model arm keeps the capture route"
            );
            if real_body {
                let before = state(&ctx);
                let mut block = Block::new(BlockId::new(0));
                assert!(
                    !lower_vec_call(&mut ctx, body, &mut block, &call, callee)
                        .unwrap_or_else(|e| panic!("{root}: Vec path: {e}")),
                    "{root}: std's body"
                );
                assert_eq!(state(&ctx), before, "{root}: no synthetic bindings");
                assert!(block.body.is_empty(), "{root}: no emission");
                assert!(block.params.is_empty(), "{root}: no synthetic parameters");
            }
            checked = true;
        }
        assert!(checked, "{root}: actual {callee_name} call checked");
    }
}

#[test]
fn aggregate_callback_custody_survives_actual_std_receiver_peeling_without_emission() {
    const CHILD: &str = "BRIDGE_AGGREGATE_CALLBACK_TEST_CHILD";
    const MARKER: &str =
        "actual std aggregate callback custody graph and negative controls checked";
    if std::env::var_os(CHILD).is_some() {
        extern crate rustc_interface;
        struct Callbacks;
        impl rustc_driver::Callbacks for Callbacks {
            fn config(&mut self, config: &mut rustc_interface::interface::Config) {
                config.input = rustc_session::config::Input::Str {
                    name: rustc_span::FileName::Custom("aggregate_callback.rs".into()),
                    input: PROBE.into(),
                };
            }
            fn after_analysis<'tcx>(
                &mut self,
                _: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                check_callback_rows(tcx);
                check_actual_nested_collection(tcx);
                check_try_fold(tcx);
                check_std_glue_capture_boundary(tcx);
                check_vec_call_closure_decisions(tcx);
                eprintln!("{MARKER}");
                rustc_driver::Compilation::Stop
            }
        }
        let sysroot = std::process::Command::new(BUILD_COMPILER)
            .args(["--print", "sysroot"])
            .output()
            .expect("resolve actual build compiler sysroot");
        assert!(
            sysroot.status.success(),
            "{}",
            String::from_utf8_lossy(&sysroot.stderr)
        );
        let arguments = vec![
            "trustc".into(),
            "--crate-type=lib".into(),
            "--emit=metadata".into(),
            "-Ztrust-verify=off".into(),
            "--sysroot".into(),
            String::from_utf8(sysroot.stdout).unwrap().trim().into(),
            "-".into(),
        ];
        rustc_driver::run_compiler(&arguments, &mut Callbacks);
        return;
    }
    let output = std::process::Command::new(std::env::current_exe().unwrap()).args([
        "--exact", "iterator_aggregate_fallback::callback_tests::aggregate_callback_custody_survives_actual_std_receiver_peeling_without_emission",
        "--nocapture",
    ]).env(CHILD, "1").output().expect("isolated actual TCX callback custody control");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    assert!(
        stderr.contains(MARKER),
        "compiler-context assertions did not execute: {stderr}"
    );
    assert!(!stderr.contains("panicked"), "{stderr}");
}
