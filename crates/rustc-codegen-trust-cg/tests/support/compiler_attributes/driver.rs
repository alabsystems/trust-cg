// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// Analyze real attributes through the production adapter, then stop before
// input code generation. These checks supply no CG/native execution credit.
#![feature(rustc_private)]

#[cfg(rustc_attr_ir_attributes)]
extern crate rustc_attr_ir;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

#[path = "../../../src/compiler_attributes.rs"]
mod compiler_attributes;

use compiler_attributes::{InlineAttr, Linkage};
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_middle::ty::TyCtxt;

struct Audit;

impl Callbacks for Audit {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let mut inline = 0;
        let (mut builtin, mut forged, mut manual) = (0, 0, 0);
        for local in tcx.iter_local_def_id() {
            let did = local.to_def_id();
            if tcx.def_kind(did) == DefKind::Fn {
                let name = tcx.item_name(did);
                let attrs = tcx.codegen_fn_attrs(did);
                match name.as_str() {
                    "plain" => assert!(matches!(attrs.inline, InlineAttr::None)),
                    "hinted" => assert!(matches!(attrs.inline, InlineAttr::Hint)),
                    "always" => assert!(matches!(attrs.inline, InlineAttr::Always)),
                    "never" => assert!(matches!(attrs.inline, InlineAttr::Never)),
                    "forced" => {
                        let InlineAttr::Force { attr_span, reason } = attrs.inline else {
                            panic!("force attribute lost");
                        };
                        assert_eq!(reason.expect("force reason").as_str(), "retained-reason");
                        let source = tcx.sess.source_map().span_to_snippet(attr_span).unwrap();
                        assert!(source.contains("rustc_force_inline"));
                        assert!(source.contains("retained-reason"));
                    }
                    _ => continue,
                }
                inline += 1;
                println!("COMPILER_INLINE name={name} value={:?}", attrs.inline);
            }
            if !matches!(tcx.def_kind(did), DefKind::Impl { .. }) {
                continue;
            }
            let automatically = tcx.is_automatically_derived(did);
            let actual_builtin = tcx.is_builtin_derived(did);
            let outer = tcx.def_span(did).ctxt().outer_expn_data();
            if actual_builtin {
                assert!(automatically);
                assert!(matches!(
                    outer.kind,
                    rustc_span::ExpnKind::Macro(rustc_span::hygiene::MacroKind::Derive, _)
                ));
                assert!(compiler_attributes::is_builtin_macro(
                    tcx,
                    outer.macro_def_id.expect("actual derive macro")
                ));
                builtin += 1;
            } else if automatically {
                assert!(matches!(
                    outer.kind,
                    rustc_span::ExpnKind::Macro(rustc_span::hygiene::MacroKind::Bang, _)
                ));
                assert!(!compiler_attributes::is_builtin_macro(
                    tcx,
                    outer.macro_def_id.expect("ordinary forging macro")
                ));
                forged += 1;
            } else {
                manual += 1;
            }
        }
        assert_eq!(inline, 5);
        assert_eq!((builtin, forged, manual), (1, 1, 1));
        let linkages = [
            Linkage::AvailableExternally,
            Linkage::ExternalWeak,
            Linkage::External,
            Linkage::Internal,
            Linkage::LinkOnceAny,
            Linkage::LinkOnceODR,
            Linkage::WeakAny,
            Linkage::WeakODR,
            #[cfg(rustc_linkage_common)]
            Linkage::Common,
        ];
        assert_eq!(
            linkages.len(),
            if cfg!(rustc_linkage_common) { 9 } else { 8 }
        );
        println!("COMPILER_ATTRIBUTES inline=5 builtin=1 forged=1 manual=1 linkages={linkages:?}");
        Compilation::Stop
    }
}

fn main() {
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Audit);
}
