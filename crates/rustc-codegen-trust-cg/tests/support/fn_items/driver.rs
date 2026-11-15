// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_middle;

#[path = "../../../src/fn_items.rs"]
mod fn_items;

pub fn construct<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    instance: rustc_middle::ty::Instance<'tcx>,
) -> rustc_middle::ty::Ty<'tcx> {
    fn_items::from_instance(tcx, instance)
}
