// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

include!(concat!(env!("OUT_DIR"), "/test_build_compiler.rs"));

const PROBE: &str = r#"
use std::iter::FromIterator;
pub struct Pair { pub value: u32, pub index: usize }
pub struct Map<I, F> { pub iterator: I, pub callback: F }
#[inline(never)] fn observe<T>(_: &T) {}
pub fn tuple_map(xs: &[u32]) {
    let it = xs.iter().map(|x| (*x, 7usize)); observe(&it);
}
pub fn struct_map(xs: &[u32]) {
    let it = xs.iter().map(|x| Pair { value: *x, index: 7 }); observe(&it);
}
pub fn wrapped_map(xs: &[u32]) {
    let it = xs.iter().map(|x| (*x, 7usize)).take(3); observe(&it);
}
pub fn scalar_map(xs: &[u32]) {
    let it = xs.iter().map(|x| *x); observe(&it);
}
pub fn pointer_map(xs: &[u32]) {
    let it = xs.iter().map(|x| (x, 7usize)); observe(&it);
}
pub fn wide_map(xs: &[u32]) {
    let it = xs.iter().map(|x| (*x as u128, 7usize)); observe(&it);
}
pub fn drop_map(xs: &[u32]) {
    let it = xs.iter().map(|x| (Box::new(*x), 7usize)); observe(&it);
}
pub fn user_map(xs: &[u32]) {
    let it = Map { iterator: xs.iter(), callback: |x: &u32| (*x, 7usize) };
    observe(&it);
}
pub fn tuple_collect(xs: &[u32]) -> Vec<(u32, usize)> {
    xs.iter().map(|x| (*x, 7usize)).collect()
}
pub fn struct_from_iter(xs: &[u32]) -> Vec<Pair> {
    Vec::from_iter(xs.iter().map(|x| Pair { value: *x, index: 7 }))
}
pub fn cached_index_collect(xs: &[u32]) -> Vec<(u32, usize)> {
    xs.iter().map(|x| *x).enumerate().map(|(index, key)| (key, index)).collect()
}
"#;

fn assert_nonmutating_vec_fallthrough<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    terminator: &mir::Terminator<'tcx>,
    callee: Instance<'tcx>,
    label: &str,
) {
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
        panic!("{label}: actual call required")
    };
    let call = DirectCallTerminator {
        func,
        args,
        destination,
        target: *target,
        unwind,
        fn_span: *fn_span,
        source_info: terminator.source_info,
    };
    let before = (
        ctx.next_value,
        ctx.next_block_id,
        ctx.extra_blocks.len(),
        ctx.module.functions.len(),
        ctx.module.func_types.len(),
        ctx.scalar_values.len(),
        ctx.vec_slot_addrs.len(),
        ctx.projected_values.len(),
        ctx.extern_callees.len(),
    );
    let mut block = Block::new(BlockId::new(0));
    assert!(
        !lower_vec_call(ctx, body, &mut block, &call, callee)
            .expect("ordinary aggregate Vec call fallthrough")
    );
    assert!(
        block.body.is_empty(),
        "{label}: no allocation, callback or branch"
    );
    assert!(block.params.is_empty(), "{label}: no synthetic parameters");
    assert_eq!(
        before,
        (
            ctx.next_value,
            ctx.next_block_id,
            ctx.extra_blocks.len(),
            ctx.module.functions.len(),
            ctx.module.func_types.len(),
            ctx.scalar_values.len(),
            ctx.vec_slot_addrs.len(),
            ctx.projected_values.len(),
            ctx.extern_callees.len(),
        ),
        "{label}: preserve original argument ownership and destination bindings"
    );
}

#[test]
fn aggregate_map_fallback_is_source_typed_shared_and_nonmutating() {
    const CHILD: &str = "BRIDGE_AGGREGATE_MAP_FALLBACK_TEST_CHILD";
    const MARKER: &str = "aggregate-map real-body rows checked: 8; actual collect calls checked: 3; actual nested spec_extend rows checked: 3";
    if std::env::var_os(CHILD).is_some() {
        extern crate rustc_interface;
        struct ProbeCallbacks;
        impl rustc_driver::Callbacks for ProbeCallbacks {
            fn config(&mut self, config: &mut rustc_interface::interface::Config) {
                config.input = rustc_session::config::Input::Str {
                    name: rustc_span::FileName::Custom("aggregate_map.rs".into()),
                    input: PROBE.into(),
                };
            }
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                for (name, expected) in [
                    ("tuple_map", true),
                    ("struct_map", true),
                    ("wrapped_map", true),
                    ("scalar_map", false),
                    ("pointer_map", false),
                    ("wide_map", false),
                    ("drop_map", false),
                    ("user_map", false),
                ] {
                    let definition = tcx
                        .hir_body_owners()
                        .find(|definition| {
                            matches!(
                                tcx.def_kind(definition.to_def_id()),
                                rustc_hir::def::DefKind::Fn
                            ) && tcx.item_name(definition.to_def_id()).as_str() == name
                        })
                        .unwrap_or_else(|| panic!("missing probe {name}"));
                    let instance = Instance::mono(tcx, definition.to_def_id());
                    let body = tcx.instance_mir(instance.def);
                    let ctx = MirLoweringCtx::new("aggregate_map", tcx, instance);
                    let locals: Vec<_> = body
                        .local_decls
                        .iter()
                        .map(|decl| decl.ty)
                        .filter(|ty| {
                            matches!(ty.kind(), ty::Adt(adt, _)
                            if adt.is_struct() && (adapter_kind_of(tcx, adt.did()).is_some()
                                || tcx.item_name(adt.did()).as_str() == "Map"))
                        })
                        .collect();
                    assert!(!locals.is_empty(), "{name}: actual iterator local missing");
                    let found = locals.iter().any(|ty| mentions_aggregate_map(tcx, *ty));
                    assert_eq!(
                        found, expected,
                        "{name}: real aggregate output classification"
                    );
                    if !expected {
                        continue;
                    }
                    for iterator in locals
                        .into_iter()
                        .filter(|ty| mentions_aggregate_map(tcx, *ty))
                    {
                        assert!(
                            ty_mentions_real_body_iterator_source(tcx, iterator),
                            "{name}: std instance types must protect live bodies from trap stubs"
                        );
                        assert!(
                            iterator_spine_has_real_body_source(&ctx, iterator).unwrap(),
                            "{name}: terminal receiver must use the same real-body decision"
                        );
                        let before = (
                            ctx.next_value,
                            ctx.next_block_id,
                            ctx.extra_blocks.len(),
                            ctx.module.functions.len(),
                            ctx.module.func_types.len(),
                        );
                        assert!(
                            resolve_iter_chain(&ctx, iterator).unwrap().is_none(),
                            "{name}: aggregate output must never enter the scalar drive"
                        );
                        assert_eq!(
                            before,
                            (
                                ctx.next_value,
                                ctx.next_block_id,
                                ctx.extra_blocks.len(),
                                ctx.module.functions.len(),
                                ctx.module.func_types.len()
                            ),
                            "{name}: fallback must precede synthetic emission"
                        );
                        let iterator_trait = tcx
                            .get_diagnostic_item(rustc_span::sym::Iterator)
                            .expect("the real Iterator trait");
                        let method = tcx
                            .associated_items(iterator_trait)
                            .in_definition_order()
                            .find(|item| item.is_fn() && item.name().as_str() == "size_hint")
                            .expect("Iterator::size_hint")
                            .def_id;
                        let size_hint = Instance::try_resolve(
                            tcx,
                            ty::TypingEnv::fully_monomorphized(),
                            method,
                            tcx.mk_args(&[iterator.into()]),
                        )
                        .expect("resolve actual size_hint")
                        .expect("size_hint instance");
                        assert!(
                            !is_dead_std_iterator_reduction_body(tcx, size_hint),
                            "{name}: the actual std method cannot be replaced by a dead-body trap"
                        );
                    }
                }
                let mut pending = Vec::new();
                for name in ["tuple_collect", "struct_from_iter", "cached_index_collect"] {
                    let definition = tcx
                        .hir_body_owners()
                        .find(|definition| {
                            matches!(
                                tcx.def_kind(definition.to_def_id()),
                                rustc_hir::def::DefKind::Fn
                            ) && tcx.item_name(definition.to_def_id()).as_str() == name
                        })
                        .unwrap_or_else(|| panic!("missing collect probe {name}"));
                    let instance = Instance::mono(tcx, definition.to_def_id());
                    let body = tcx.instance_mir(instance.def);
                    let mut ctx = MirLoweringCtx::new("aggregate_collect", tcx, instance);
                    let mut checked = 0;
                    for data in body.basic_blocks.iter() {
                        let terminator = data.terminator();
                        let TerminatorKind::Call {
                            func,
                            args,
                            destination,
                            fn_span,
                            ..
                        } = &terminator.kind
                        else {
                            continue;
                        };
                        let callee = direct_callee_instance(&ctx, body, func, *fn_span)
                            .expect("actual monomorphized direct call");
                        let method = callee_item_name_str(tcx, callee.def_id());
                        if !matches!(method.as_str(), "collect" | "from_iter") {
                            continue;
                        }
                        assert!(is_std_collection_method_callee(tcx, callee.def_id()));
                        let element = vec_element_ty(tcx, place_rust_ty(&ctx, body, destination))
                            .expect("real Vec destination with an existing image");
                        assert!(vec_struct_element_admissible(tcx, element));
                        let iterator = ctx
                            .monomorphize_ty(operand_rust_ty(&ctx, body, &args[0].node).unwrap());
                        assert!(mentions_aggregate_map(tcx, iterator));
                        assert!(iterator_spine_has_real_body_source(&ctx, iterator).unwrap());
                        assert!(ty_mentions_real_body_iterator_source(tcx, iterator));
                        assert!(
                            !is_dead_std_iterator_reduction_body(tcx, callee),
                            "{name}: the ordinary constructor must stay live"
                        );
                        assert_nonmutating_vec_fallthrough(
                            &mut ctx, body, terminator, callee, name,
                        );
                        pending.push((name, callee));
                        checked += 1;
                    }
                    assert_eq!(checked, 1, "{name}: check the actual source collect call");
                }
                // Follow only the actual typed collection entry bodies until
                // their real specialized Vec receiver calls spec_extend. No
                // private method DefId, type arguments or source call is forged.
                let mut visited = HashSet::new();
                let mut nested_rows = HashSet::new();
                while let Some((name, instance)) = pending.pop() {
                    if !visited.insert((name, instance)) {
                        continue;
                    }
                    assert!(
                        visited.len() <= 24,
                        "bounded actual collection entry traversal"
                    );
                    let body = tcx.instance_mir(instance.def);
                    let mut ctx = MirLoweringCtx::new("aggregate_nested_collect", tcx, instance);
                    for data in body.basic_blocks.iter() {
                        let terminator = data.terminator();
                        let TerminatorKind::Call {
                            func,
                            args,
                            fn_span,
                            ..
                        } = &terminator.kind
                        else {
                            continue;
                        };
                        let callee = direct_callee_instance(&ctx, body, func, *fn_span)
                            .expect("actual std collection direct call");
                        if !is_std_collection_method_callee(tcx, callee.def_id()) {
                            continue;
                        }
                        let actual_map_argument = args.iter().any(|argument| {
                            let ty = ctx.monomorphize_ty(
                                operand_rust_ty(&ctx, body, &argument.node).unwrap(),
                            );
                            mentions_aggregate_map(tcx, ty)
                        });
                        if !actual_map_argument {
                            continue;
                        }
                        let method = callee_item_name_str(tcx, callee.def_id());
                        match method.as_str() {
                            "collect" | "from_iter" => pending.push((name, callee)),
                            "spec_extend" => {
                                assert_eq!(args.len(), 2, "real Vec receiver and iterator");
                                let receiver = ctx.monomorphize_ty(
                                    operand_rust_ty(&ctx, body, &args[0].node).unwrap(),
                                );
                                let ty::Ref(_, vector, rustc_hir::Mutability::Mut) =
                                    *receiver.kind()
                                else {
                                    panic!("{name}: actual &mut Vec")
                                };
                                let element = vec_element_ty(tcx, vector)
                                    .expect("actual specialized Vec receiver image");
                                assert!(vec_struct_element_admissible(tcx, element));
                                let iterator = ctx.monomorphize_ty(
                                    operand_rust_ty(&ctx, body, &args[1].node).unwrap(),
                                );
                                assert!(mentions_aggregate_map(tcx, iterator));
                                assert!(ty_mentions_real_body_iterator_source(tcx, iterator));
                                assert!(
                                    !is_dead_std_iterator_reduction_body(tcx, callee),
                                    "{name}: the real extension body must not become a trap"
                                );
                                assert_nonmutating_vec_fallthrough(
                                    &mut ctx, body, terminator, callee, name,
                                );
                                nested_rows.insert(name);
                            }
                            _ => {}
                        }
                    }
                }
                assert_eq!(
                    nested_rows.len(),
                    3,
                    "all three real nested Vec extension calls"
                );
                eprintln!("{MARKER}");
                rustc_driver::Compilation::Stop
            }
        }
        let sysroot = std::process::Command::new(BUILD_COMPILER)
            .args(["--print", "sysroot"])
            .output()
            .expect("resolve build compiler sysroot");
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
        rustc_driver::run_compiler(&arguments, &mut ProbeCallbacks);
        return;
    }
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "iterator_aggregate_fallback::tests::aggregate_map_fallback_is_source_typed_shared_and_nonmutating", "--nocapture"])
        .env(CHILD, "1").output().expect("isolated compiler-context aggregate-map control");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    assert!(
        stderr.contains(MARKER),
        "compiler-context controls never executed: {stderr}"
    );
    assert!(!stderr.contains("panicked"), "{stderr}");
}
