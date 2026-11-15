// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Actual function-item types plus seeded typed binders; stop before codegen.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

#[path = "../../../src/fn_items.rs"]
mod fn_items;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Instance, TyCtxt};
use std::collections::BTreeSet;

fn check_free<'tcx>(
    kind: &ty::TyKind<'tcx>,
    def_id: DefId,
    expected: fn_items::GenericArgsRef<'tcx>,
) {
    let before = *kind;
    let item = fn_items::view(kind).expect("function-item view");
    assert_eq!(item.def_id(), def_id, "original definition id");
    assert!(
        std::ptr::eq(item.original(), kind),
        "original kind reference"
    );
    let free = item.unbound_args().expect("free arguments");
    // The by-value handle compares the interned list it wraps; the alias is
    // that list's reference and is compared by address.
    #[cfg(rustc_generic_args_value)]
    let same_list = free == expected;
    #[cfg(not(rustc_generic_args_value))]
    let same_list = std::ptr::eq(free, expected);
    assert!(same_list, "complete original argument list");
    assert_eq!(
        item.require_unbound_args("actual query").unwrap(),
        expected,
        "required original argument list"
    );
    assert_eq!(*kind, before, "original descriptor changed");
}

fn seeded<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, nested: ty::Ty<'tcx>) {
    let constants = [0, 1, 7, 65535, u64::from(u32::MAX), u64::MAX]
        .map(|n| ty::Const::from_target_usize(tcx, n).into());
    let lists: Vec<Vec<ty::GenericArg<'tcx>>> = vec![
        vec![],
        vec![tcx.types.u32.into()],
        vec![tcx.types.u128.into(), tcx.types.u8.into()],
        constants.to_vec(),
        vec![
            tcx.lifetimes.re_static.into(),
            tcx.lifetimes.re_erased.into(),
        ],
        vec![nested.into()],
        vec![
            tcx.lifetimes.re_static.into(),
            tcx.types.u64.into(),
            constants[5],
            tcx.types.f64.into(),
            tcx.lifetimes.re_erased.into(),
            constants[0],
            tcx.types.u64.into(),
        ],
    ];
    for values in &lists {
        let args = tcx.mk_args(values);
        #[cfg(rustc_bound_fn_args)]
        let stored = ty::Binder::dummy(args);
        #[cfg(not(rustc_bound_fn_args))]
        let stored = args;
        check_free(&ty::FnDef(def_id, stored), def_id, args);
    }
    assert_eq!(lists.len(), 7);
    #[cfg(rustc_bound_fn_args)]
    {
        let variable_kinds = [
            ty::BoundVariableKind::Region(ty::BoundRegionKind::Anon),
            ty::BoundVariableKind::Ty(ty::BoundTyKind::Anon),
            ty::BoundVariableKind::Const,
        ];
        // A declared variable unused by the value does not escape. The view
        // keeps those original declarations while reading the free value.
        for count in 1..=variable_kinds.len() {
            let vars = tcx.mk_bound_variable_kinds(&variable_kinds[..count]);
            let args = tcx.mk_args(&lists[6]);
            let original = ty::FnDef(def_id, ty::Binder::bind_with_vars(args, vars));
            check_free(&original, def_id, args);
        }
        let mut rejected = 0;
        for depth in [0, 1] {
            let index = ty::DebruijnIndex::from_u32(depth);
            let variable = ty::BoundVar::from_u32(0);
            let region = ty::Region::new_bound(
                tcx,
                index,
                ty::BoundRegion {
                    var: variable,
                    kind: ty::BoundRegionKind::Anon,
                },
            );
            let bound_ty = ty::Ty::new_bound(
                tcx,
                index,
                ty::BoundTy {
                    var: variable,
                    kind: ty::BoundTyKind::Anon,
                },
            );
            let constant = ty::Const::new_bound(tcx, index, ty::BoundConst::new(variable));
            let values: [ty::GenericArg<'tcx>; 3] =
                [region.into(), bound_ty.into(), constant.into()];
            for (value, kind) in values.into_iter().zip(variable_kinds) {
                let vars = tcx.mk_bound_variable_kinds(&[kind]);
                for with_suffix in [false, true] {
                    let args = if with_suffix {
                        tcx.mk_args(&[value, tcx.types.u64.into(), constants[5]])
                    } else {
                        tcx.mk_args(&[value])
                    };
                    let original = ty::FnDef(def_id, ty::Binder::bind_with_vars(args, vars));
                    let before = original;
                    let item = fn_items::view(&original).unwrap();
                    assert!(
                        item.unbound_args().is_none(),
                        "escaping arguments were stripped"
                    );
                    let refusal = item.require_unbound_args("seeded bound").unwrap_err();
                    assert!(refusal.contains(fn_items::BOUND_ARGS_REFUSAL));
                    assert!(refusal.contains("seeded bound"));
                    assert!(std::ptr::eq(item.original(), &original));
                    assert_eq!(original, before, "bound descriptor changed");
                    rejected += 1;
                }
            }
        }
        assert_eq!(rejected, 12);
        println!("FN_ITEMS_BINDERS unused=3 escaping_refusals=12");
    }
    println!("FN_ITEMS_SEEDED free=7 nested_function_pointer=1");
}

struct Audit;
impl Callbacks for Audit {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let mut functions = BTreeSet::new();
        let mut nested = None;
        let mut seed_definition = None;
        let mut const_constructors = 0;
        for local in tcx.iter_local_def_id() {
            let did = local.to_def_id();
            if tcx.def_kind(did) != rustc_hir::def::DefKind::Fn {
                continue;
            }
            let name = tcx.item_name(did).as_str().to_owned();
            if !name.starts_with("case_") {
                continue;
            }
            let value = tcx.type_of(did).instantiate_identity().skip_normalization();
            let expected = ty::GenericArgs::identity_for_item(tcx, did);
            check_free(value.kind(), did, expected);
            let constructed = fn_items::from_instance(
                tcx,
                Instance {
                    def: ty::InstanceKind::Item(did),
                    args: expected,
                },
            );
            // This is a fresh type from Instance arguments. Original source
            // types may retain unused region declarations in their binder;
            // those remain on the borrowed original, not on this new item.
            check_free(constructed.kind(), did, expected);
            #[cfg(rustc_bound_fn_args)]
            {
                let ty::FnDef(_, binder) = *constructed.kind() else {
                    unreachable!()
                };
                assert!(binder.bound_vars().is_empty(), "fresh instance binder");
            }
            if name == "case_const" {
                for count in [0, 1, 7, 65535, u64::from(u32::MAX), u64::MAX] {
                    let args = tcx.mk_args(&[ty::Const::from_target_usize(tcx, count).into()]);
                    let fresh = fn_items::from_instance(
                        tcx,
                        Instance {
                            def: ty::InstanceKind::Item(did),
                            args,
                        },
                    );
                    check_free(fresh.kind(), did, args);
                    #[cfg(rustc_bound_fn_args)]
                    {
                        let ty::FnDef(_, binder) = *fresh.kind() else {
                            unreachable!()
                        };
                        assert!(
                            binder.bound_vars().is_empty(),
                            "fresh const instance binder"
                        );
                    }
                    const_constructors += 1;
                }
            }
            if name == "case_higher" {
                nested = Some(
                    tcx.fn_sig(did)
                        .instantiate_identity()
                        .skip_binder()
                        .inputs()[0],
                );
            }
            if name == "case_plain" {
                seed_definition = Some(did);
            }
            assert!(functions.insert(name));
        }
        assert_eq!(functions.len(), 12, "all actual function declarations");
        seeded(tcx, seed_definition.unwrap(), nested.unwrap());
        assert_eq!(const_constructors, 6);
        println!("FN_ITEMS_CONST_CONSTRUCTORS cases=6");
        println!("FN_ITEMS_REAL functions=12 fresh_constructors=18 original_descriptors=30");
        Compilation::Stop
    }
}

fn main() {
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Audit);
}
