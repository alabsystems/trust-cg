// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// Inspect actual Rust layouts through the production pair view, then stop
// before input codegen. Synthetic descriptors test explicit offset transport;
// they do not establish native support for new or noncanonical Rust layouts.
#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

#[path = "../../../src/scalar_pair.rs"]
mod scalar_pair;

use rustc_abi::{BackendRepr, Scalar};
use rustc_driver::{Callbacks, Compilation};
use rustc_middle::ty::layout::LayoutCx;
use rustc_middle::ty::{self, Ty, TyCtxt};

struct Audit;

fn primitive<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Scalar {
    let layout = tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .unwrap();
    let BackendRepr::Scalar(scalar) = layout.backend_repr else {
        panic!("primitive layout changed: {ty:?}");
    };
    scalar
}

impl Callbacks for Audit {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        assert_eq!(tcx.data_layout.pointer_size().bytes(), 8);
        let env = ty::TypingEnv::fully_monomorphized();
        let cx = LayoutCx::new(tcx, env);
        let mut queries = 0;
        let mut pairs = 0;
        let mut physical = 0;
        for local in tcx.iter_local_def_id() {
            let did = local.to_def_id();
            if tcx.def_kind(did) != rustc_hir::def::DefKind::TyAlias {
                continue;
            }
            let name = tcx.item_name(did);
            if !name.as_str().starts_with("Case") {
                continue;
            }
            let ty = tcx.normalize_erasing_regions(env, tcx.type_of(did).instantiate_identity());
            let layout = tcx.layout_of(env.as_query_input(ty)).unwrap();
            let pair = scalar_pair::view(layout.backend_repr);
            if matches!(
                name.as_str(),
                "CaseU8" | "CaseU64" | "CaseBool" | "CaseF64" | "CaseThin"
            ) {
                assert!(pair.is_none(), "nonpair {name}");
            }
            if matches!(
                name.as_str(),
                "CaseSlice"
                    | "CaseStr"
                    | "CaseDyn"
                    | "CaseTransparent"
                    | "CaseNonNull"
                    | "CaseNullableSlice"
                    | "CaseTupleInts"
                    | "CaseF32Pair"
                    | "CaseF64Pair"
            ) {
                assert!(pair.is_some(), "required pair {name}");
            }
            if let Some(pair) = pair {
                let offset = pair.second_offset(&tcx).bytes();
                assert!(offset >= pair.a.size(&tcx).bytes());
                assert!(offset + pair.b.size(&tcx).bytes() <= layout.size.bytes());
                let is_enum = matches!(ty.kind(), ty::Adt(adt, _) if adt.is_enum());
                if !is_enum {
                    let mut inner = layout;
                    let mut checked = false;
                    for _ in 0..16 {
                        let fields: Vec<_> = (0..inner.fields.count())
                            .filter(|index| !inner.field(&cx, *index).is_zst())
                            .collect();
                        if fields.len() == 1 {
                            let index = fields[0];
                            assert_eq!(inner.fields.offset(index).bytes(), 0);
                            inner = inner.field(&cx, index);
                        } else {
                            assert_eq!(fields.len(), 2, "physical pair fields {name}");
                            let mut offsets: Vec<_> = fields
                                .iter()
                                .map(|index| inner.fields.offset(*index).bytes())
                                .collect();
                            offsets.sort_unstable();
                            assert_eq!(offsets, [0, offset], "physical pair memory order {name}");
                            checked = true;
                            physical += 1;
                            break;
                        }
                    }
                    assert!(checked, "transparent layout recursion {name}");
                }
                pairs += 1;
                println!(
                    "RUST_PAIR name={name} offset={offset} size={} a={:?} b={:?}",
                    layout.size.bytes(),
                    pair.a,
                    pair.b
                );
            } else {
                println!("RUST_NONPAIR name={name} repr={:?}", layout.backend_repr);
            }
            queries += 1;
        }
        assert_eq!(queries, 21);
        assert!(pairs >= 9);
        assert!(physical >= 8);
        let boolean = primitive(tcx, tcx.types.bool);
        let byte = primitive(tcx, tcx.types.u8);
        let word = primitive(tcx, tcx.types.u64);
        let f32 = primitive(tcx, tcx.types.f32);
        let f64 = primitive(tcx, tcx.types.f64);
        let mut synthetic = 0;
        for (a, b, natural) in [
            (boolean, word, 8u64),
            (byte, word, 8),
            (f32, f32, 4),
            (f64, f64, 8),
            (word.to_union(), boolean, 8),
            (boolean, word.to_union(), 8),
        ] {
            #[cfg(rustc_scalar_pair_struct)]
            let offsets = vec![natural, natural + 1, natural + 8, natural + 16];
            #[cfg(not(rustc_scalar_pair_struct))]
            let offsets = vec![natural];
            for expected in offsets {
                #[cfg(rustc_scalar_pair_struct)]
                let repr = BackendRepr::ScalarPair {
                    a,
                    b,
                    b_offset: rustc_abi::Size::from_bytes(expected),
                };
                #[cfg(not(rustc_scalar_pair_struct))]
                let repr = BackendRepr::ScalarPair(a, b);
                let pair = scalar_pair::view(repr).expect("synthetic pair");
                assert_eq!(pair.a, a, "first scalar including validity");
                assert_eq!(pair.b, b, "second scalar including validity");
                assert_eq!(
                    pair.second_offset(&tcx).bytes(),
                    expected,
                    "declared or implicit second offset"
                );
                synthetic += 1;
            }
        }
        for repr in [
            BackendRepr::Scalar(boolean),
            BackendRepr::Memory { sized: true },
            BackendRepr::Memory { sized: false },
        ] {
            assert!(scalar_pair::view(repr).is_none());
        }
        assert_eq!(
            synthetic,
            if cfg!(rustc_scalar_pair_struct) {
                24
            } else {
                6
            }
        );
        println!(
            "SCALAR_PAIR_QUERIES layouts={queries} pairs={pairs} physical={physical} synthetic={synthetic} nonpairs=3 explicit_offset={}",
            cfg!(rustc_scalar_pair_struct)
        );
        Compilation::Stop
    }
}

fn main() {
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Audit);
}
