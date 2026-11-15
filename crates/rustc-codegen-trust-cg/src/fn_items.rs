// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Function-item views retain the original binder. Resolution reads argument
//! values only when they contain no escaping bound variables.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Instance, Ty, TyCtxt, TyKind};

/// The interned generic-argument list of a function item or instance, under
/// whichever name the compiler gives it. Both spellings are `Copy` handles to
/// the same interned list; no argument is read or rebuilt by the choice.
#[cfg(not(rustc_generic_args_value))]
pub(super) type GenericArgsRef<'tcx> = ty::GenericArgsRef<'tcx>;
#[cfg(rustc_generic_args_value)]
pub(super) type GenericArgsRef<'tcx> = ty::GenericArgs<'tcx>;

pub(super) const BOUND_ARGS_REFUSAL: &str = "[TCG-FN-ITEM-BOUND-ARGS]";

#[derive(Clone, Copy)]
pub(super) struct View<'a, 'tcx> {
    original: &'a TyKind<'tcx>,
}

impl<'a, 'tcx> View<'a, 'tcx> {
    pub(super) fn original(self) -> &'a TyKind<'tcx> {
        self.original
    }

    pub(super) fn def_id(self) -> DefId {
        let ty::FnDef(def_id, _) = *self.original() else {
            unreachable!("function-item view is created only from FnDef")
        };
        def_id
    }

    pub(super) fn unbound_args(self) -> Option<GenericArgsRef<'tcx>> {
        let ty::FnDef(_, args) = *self.original() else {
            unreachable!("function-item view is created only from FnDef")
        };
        #[cfg(rustc_bound_fn_args)]
        {
            args.no_bound_vars()
        }
        #[cfg(not(rustc_bound_fn_args))]
        {
            Some(args)
        }
    }

    pub(super) fn require_unbound_args(
        self,
        context: &str,
    ) -> Result<GenericArgsRef<'tcx>, String> {
        self.unbound_args().ok_or_else(|| {
            format!("{BOUND_ARGS_REFUSAL} {context}: function item retains bound variables")
        })
    }
}

pub(super) fn view<'a, 'tcx>(kind: &'a TyKind<'tcx>) -> Option<View<'a, 'tcx>> {
    match kind {
        ty::FnDef(_, _) => Some(View { original: kind }),
        _ => None,
    }
}

/// Instance arguments are already outside a binder. Construct only that exact
/// function item; an existing bound item must stay in its original view.
pub(super) fn from_instance<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> Ty<'tcx> {
    let args = instance.args;
    #[cfg(rustc_bound_fn_args)]
    let args = ty::Binder::dummy(args);
    Ty::new_fn_def(tcx, instance.def_id(), args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_hir::def_id::{CrateNum, DefIndex};

    /// Address identity of two interned generic-argument lists, under either
    /// spelling of the handle. Equal contents at different addresses fail.
    fn same_interned_list<'tcx>(a: GenericArgsRef<'tcx>, b: GenericArgsRef<'tcx>) -> bool {
        #[cfg(not(rustc_generic_args_value))]
        {
            std::ptr::eq(a, b)
        }
        #[cfg(rustc_generic_args_value)]
        {
            std::ptr::eq(a.as_slice().as_ptr(), b.as_slice().as_ptr())
        }
    }

    #[test]
    fn empty_argument_views_preserve_definition_and_original_kind() {
        #[cfg(not(rustc_generic_args_value))]
        let args: GenericArgsRef<'_> = ty::List::empty();
        #[cfg(rustc_generic_args_value)]
        let args: GenericArgsRef<'_> = ty::GenericArgs::empty();
        for (krate, index) in [(0, 0), (0, 7), (1, 0), (7, 65535)] {
            let def_id = DefId {
                krate: CrateNum::from_u32(krate),
                index: DefIndex::from_u32(index),
            };
            #[cfg(rustc_bound_fn_args)]
            let stored = ty::Binder::dummy(args);
            #[cfg(not(rustc_bound_fn_args))]
            let stored = args;
            let original = ty::FnDef(def_id, stored);
            let before = original;
            let item = view(&original).expect("function-item fixture");
            assert_eq!(item.def_id(), def_id, "function definition changed");
            assert!(
                std::ptr::eq(item.original(), &original),
                "original kind borrow"
            );
            assert_eq!(original, before, "original function item changed");
            assert!(
                same_interned_list(item.unbound_args().expect("empty binder"), args),
                "original generic-argument list"
            );
            assert!(
                same_interned_list(item.require_unbound_args("unit").unwrap(), args),
                "required generic-argument list"
            );
        }
        println!("FN_ITEMS_EMPTY cases=4");
    }

    #[test]
    fn non_function_kinds_do_not_acquire_a_function_item_view() {
        for original in [ty::Bool, ty::Char, ty::Str, ty::Never] {
            let before = original;
            assert!(view(&original).is_none(), "non-function acquired item view");
            assert_eq!(original, before, "non-function kind changed");
        }
        println!("FN_ITEMS_OTHER cases=4");
    }
}
