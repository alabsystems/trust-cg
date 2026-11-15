// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// Actual compiler MIR transport checks. Stop before input codegen.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path = "../../../src/synthetic_terminator.rs"]
mod synthetic_terminator;

use rustc_driver::{Callbacks, Compilation};
use rustc_middle::mir::{
    BasicBlock, Local, Place, TerminatorKind, UnwindAction, UnwindTerminateReason,
};
use rustc_middle::ty::TyCtxt;
use std::collections::BTreeSet;

struct Audit;
impl Callbacks for Audit {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let mut functions = BTreeSet::new();
        let (mut terms, mut drops, mut asserts, mut returns, mut projected) = (0, 0, 0, 0, 0);
        for local in tcx.iter_local_def_id() {
            let did = local.to_def_id();
            if tcx.def_kind(did) != rustc_hir::def::DefKind::Fn {
                continue;
            }
            let name = tcx.item_name(did).as_str().to_owned();
            if !name.starts_with("case_") {
                continue;
            }
            let body = tcx.optimized_mir(did);
            let mut blocks = 0;
            for block in body.basic_blocks.iter() {
                let original = block.terminator();
                let actual = synthetic_terminator::new(original.source_info, original.kind.clone());
                assert_eq!(actual.source_info, original.source_info, "real MIR source");
                assert_eq!(actual.kind, original.kind, "complete real MIR operation");
                #[cfg(rustc_terminator_attributes)]
                assert!(
                    actual.attributes.is_empty(),
                    "fresh operation has no global attributes"
                );
                match &original.kind {
                    TerminatorKind::Drop {
                        place,
                        target,
                        unwind,
                        replace,
                        drop,
                    } => {
                        let _ = (place, target, unwind, replace, drop);
                        drops += 1;
                    }
                    TerminatorKind::Assert {
                        cond,
                        expected,
                        msg,
                        target,
                        unwind,
                    } => {
                        let _ = (cond, expected, msg, target, unwind);
                        asserts += 1;
                    }
                    TerminatorKind::Return => returns += 1,
                    _ => {}
                }
                blocks += 1;
                terms += 1;
            }
            if name == "case_borrowed" {
                assert_eq!(body.arg_count, 1);
                let source = body
                    .basic_blocks
                    .iter()
                    .next()
                    .unwrap()
                    .terminator()
                    .source_info;
                let place = tcx.mk_place_deref(Place::from(Local::from_u32(1)));
                assert_eq!(place.projection.len(), 1);
                for target in [1, 7] {
                    for unwind in [
                        UnwindAction::Continue,
                        UnwindAction::Unreachable,
                        UnwindAction::Cleanup(BasicBlock::from_u32(13)),
                        UnwindAction::Terminate(UnwindTerminateReason::Abi),
                        UnwindAction::Terminate(UnwindTerminateReason::InCleanup),
                    ] {
                        for replace in [false, true] {
                            for drop in [None, Some(3), Some(23)] {
                                let kind = TerminatorKind::Drop {
                                    place,
                                    target: BasicBlock::from_u32(target),
                                    unwind,
                                    replace,
                                    drop: drop.map(BasicBlock::from_u32),
                                };
                                let actual = synthetic_terminator::new(source, kind.clone());
                                assert_eq!(actual.source_info, source);
                                assert_eq!(actual.kind, kind, "projected drop payload");
                                projected += 1;
                            }
                        }
                    }
                }
            }
            assert!(functions.insert(name.clone()));
            println!("REAL_SYNTHETIC_TERM function={name} blocks={blocks}");
        }
        let expected: BTreeSet<String> = [
            "case_simple",
            "case_drop",
            "case_conditional",
            "case_borrowed",
            "case_bounds",
            "case_overflow",
            "case_divide",
            "case_loop",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect();
        assert_eq!(functions, expected);
        assert!(drops > 0 && asserts > 0 && returns > 0);
        assert_eq!(projected, 60);
        println!(
            "SYNTHETIC_TERM_REAL functions={} terms={terms} drops={drops} asserts={asserts} returns={returns} projected={projected} global_attributes={}",
            functions.len(),
            cfg!(rustc_terminator_attributes)
        );
        Compilation::Stop
    }
}
fn main() {
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Audit);
}
