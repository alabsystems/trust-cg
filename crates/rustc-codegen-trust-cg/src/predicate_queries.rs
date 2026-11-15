// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Keep the complete clauses, source spans, binders and generic parent returned
//! by each compiler query. Explicit supers and usage-site clauses are distinct.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Span;

pub(super) type Clauses<'tcx> = &'tcx [(ty::Clause<'tcx>, Span)];

pub(super) fn explicit_supers<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> ty::EarlyBinder<'tcx, Clauses<'tcx>> {
    #[cfg(rustc_super_clauses_query)]
    {
        tcx.explicit_super_clauses_of(def_id)
    }
    #[cfg(not(rustc_super_clauses_query))]
    {
        tcx.explicit_super_predicates_of(def_id)
    }
}

pub(super) fn own<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> (Option<DefId>, Clauses<'tcx>) {
    #[cfg(rustc_own_clauses_query)]
    {
        let value = tcx.clauses_of(def_id);
        (value.parent, value.clauses)
    }
    #[cfg(not(rustc_own_clauses_query))]
    {
        let value = tcx.predicates_of(def_id);
        (value.parent, value.predicates)
    }
}
