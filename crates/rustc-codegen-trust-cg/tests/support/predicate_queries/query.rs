// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Query real generic, supertrait and higher-rank clauses without input codegen.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

#[path = "../../../src/predicate_queries.rs"]
mod predicate_queries;

use rustc_driver::{Callbacks, Compilation};
use rustc_middle::ty::TyCtxt;
use std::collections::BTreeSet;

fn local_traits<'tcx>(
    tcx: TyCtxt<'tcx>,
    clauses: predicate_queries::Clauses<'tcx>,
) -> BTreeSet<String> {
    clauses
        .iter()
        .filter_map(|(clause, _)| clause.as_trait_clause())
        .filter(|clause| clause.def_id().is_local())
        .map(|clause| tcx.item_name(clause.def_id()).as_str().to_owned())
        .collect()
}

struct Audit;
impl Callbacks for Audit {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let mut items = BTreeSet::new();
        let (mut traits, mut parents, mut higher) = (0, 0, 0);
        for local in tcx.iter_local_def_id() {
            let did = local.to_def_id();
            let kind = tcx.def_kind(did);
            if !matches!(
                kind,
                rustc_hir::def::DefKind::Trait
                    | rustc_hir::def::DefKind::Fn
                    | rustc_hir::def::DefKind::AssocFn
                    | rustc_hir::def::DefKind::Struct
            ) {
                continue;
            }
            let name = tcx.item_name(did).as_str().to_owned();
            if !name.starts_with("Case") && !name.starts_with("case_") {
                continue;
            }
            #[cfg(rustc_own_clauses_query)]
            let raw = tcx.clauses_of(did);
            #[cfg(not(rustc_own_clauses_query))]
            let raw = tcx.predicates_of(did);
            #[cfg(rustc_own_clauses_query)]
            let expected = raw.clauses;
            #[cfg(not(rustc_own_clauses_query))]
            let expected = raw.predicates;
            let (parent, clauses) = predicate_queries::own(tcx, did);
            assert_eq!(parent, raw.parent, "original generic parent");
            assert_eq!(
                clauses, expected,
                "complete clauses, spans and bound variables"
            );
            assert!(
                std::ptr::eq(clauses, expected),
                "original ordered clause/span slice"
            );
            #[cfg(rustc_own_clauses_query)]
            let written = tcx.explicit_clauses_of(did).clauses;
            #[cfg(not(rustc_own_clauses_query))]
            let written = tcx.explicit_predicates_of(did).predicates;
            if name == "CaseInferred" {
                assert_eq!(written.len(), 1, "explicit struct bounds");
                assert_eq!(clauses.len(), 2, "inferred outlives retained");
            }
            if name == "case_plain" {
                assert!(clauses.is_empty(), "empty query remains empty");
            }
            if name == "case_method" || name == "case_trait_method" {
                assert_eq!(parent, Some(tcx.parent(did)), "method generic parent");
                assert!(
                    !predicate_queries::own(tcx, parent.unwrap()).1.is_empty(),
                    "parent clauses retained"
                );
                assert_eq!(clauses.len(), 3, "only this method's own clauses");
                parents += 1;
            }
            if name == "case_higher" || name == "CaseHigher" {
                assert!(
                    clauses
                        .iter()
                        .any(|(c, _)| !c.kind().bound_vars().is_empty()),
                    "higher-rank declarations retained"
                );
                higher += 1;
            }
            if kind == rustc_hir::def::DefKind::Trait {
                traits += 1;
                assert_eq!(
                    clauses.len(),
                    written.len() + 1,
                    "usage-site Self trait clause retained"
                );
                assert!(
                    clauses.last().unwrap().1.is_dummy(),
                    "synthetic Self trait source span"
                );
                #[cfg(rustc_super_clauses_query)]
                let raw_super = tcx.explicit_super_clauses_of(did);
                #[cfg(not(rustc_super_clauses_query))]
                let raw_super = tcx.explicit_super_predicates_of(did);
                let retained = predicate_queries::explicit_supers(tcx, did);
                assert_eq!(
                    retained.skip_binder(),
                    raw_super.skip_binder(),
                    "original super clauses and spans"
                );
                assert!(
                    std::ptr::eq(retained.skip_binder(), raw_super.skip_binder()),
                    "original explicit super slice"
                );
                if name == "CaseLeaf" {
                    assert_eq!(
                        local_traits(tcx, retained.skip_binder()),
                        BTreeSet::from(["CaseMid".to_owned()]),
                        "no transitive supertrait expansion"
                    );
                }
                if name == "CaseAssoc" {
                    assert_eq!(
                        local_traits(tcx, retained.skip_binder()),
                        BTreeSet::from(["CaseAssocBase".to_owned()]),
                        "no implied associated-type edge"
                    );
                    #[cfg(rustc_super_clauses_query)]
                    let implied = tcx.explicit_implied_clauses_of(did);
                    #[cfg(not(rustc_super_clauses_query))]
                    let implied = tcx.explicit_implied_predicates_of(did);
                    assert_eq!(retained.skip_binder().len(), 2);
                    assert_eq!(
                        implied.skip_binder().len(),
                        3,
                        "causal implied-query contrast"
                    );
                }
                if name == "CaseHigher" {
                    assert!(
                        retained
                            .skip_binder()
                            .iter()
                            .any(|(c, _)| c.kind().bound_vars().len() == 1),
                        "supertrait higher-rank binder"
                    );
                }
            }
            assert!(items.insert(name), "unique source item");
        }
        assert_eq!((items.len(), traits, parents, higher), (16, 9, 2, 2));
        println!("PREDICATE_QUERY_REAL items=16 traits=9 parents=2 higher_rank=2");
        Compilation::Stop
    }
}
fn main() {
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Audit);
}
