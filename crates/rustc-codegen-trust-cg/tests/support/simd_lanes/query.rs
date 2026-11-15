// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Actual compiler pointee layouts; stop before input codegen.
#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

#[path = "../../../src/simd_lanes.rs"]
mod simd_lanes;

use rustc_driver::{Callbacks, Compilation};
use rustc_middle::ty::{self, TyCtxt};
use std::collections::BTreeSet;

struct Audit;
impl Callbacks for Audit {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let mut functions = BTreeSet::new();
        let mut vectors = 0;
        for local in tcx.iter_local_def_id() {
            let did = local.to_def_id();
            if tcx.def_kind(did) != rustc_hir::def::DefKind::Fn {
                continue;
            }
            let name = tcx.item_name(did).as_str().to_owned();
            if !name.starts_with("case_") {
                continue;
            }
            let expected = match name.as_str() {
                "case_scalar" | "case_array_one" | "case_uint" => (None, 2, 2),
                "case_array_zero" => (None, 0, 2),
                "case_array_three" => (None, 6, 2),
                "case_array_four" => (None, 8, 2),
                "case_array_eight" => (None, 16, 2),
                "case_vector_four" | "case_integer_vector_four" | "case_raw_vector_four" => {
                    (Some(4), 8, 8)
                }
                "case_vector_eight" | "case_mut_vector_eight" => (Some(8), 16, 16),
                _ => panic!("unexpected layout case {name}"),
            };
            let body = tcx.optimized_mir(did);
            assert_eq!(body.arg_count, 1);
            let argument = body.args_iter().next().expect("one real input");
            let pointee = match body.local_decls[argument].ty.kind() {
                ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => *pointee,
                other => panic!("unexpected input type {other:?}"),
            };
            let layout = tcx
                .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(pointee))
                .expect("actual pointee layout");
            let original = layout.backend_repr;
            assert_eq!(
                simd_lanes::count(&layout.backend_repr),
                expected.0,
                "actual fixed-vector lane count for {name}"
            );
            assert_eq!(
                layout.size.bytes(),
                expected.1,
                "actual pointee byte size for {name}"
            );
            assert_eq!(
                layout.align.bytes(),
                expected.2,
                "actual pointee ABI alignment for {name}"
            );
            assert_eq!(
                layout.backend_repr, original,
                "actual descriptor changed for {name}"
            );
            vectors += usize::from(expected.0.is_some());
            assert!(functions.insert(name), "duplicate layout case");
        }
        assert_eq!(
            functions,
            [
                "case_scalar",
                "case_array_zero",
                "case_array_one",
                "case_array_three",
                "case_array_four",
                "case_array_eight",
                "case_vector_four",
                "case_vector_eight",
                "case_integer_vector_four",
                "case_uint",
                "case_raw_vector_four",
                "case_mut_vector_eight"
            ]
            .into_iter()
            .map(str::to_owned)
            .collect()
        );
        assert_eq!(vectors, 5);
        println!("SIMD_LANES_REAL functions=12 vectors=5 original_descriptors=12");
        Compilation::Stop
    }
}

fn main() {
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Audit);
}
