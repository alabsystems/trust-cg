// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// Actual compiler bodies and seeded metadata descriptors; no input codegen.
#![feature(rustc_private)]
#[cfg(rustc_goto_loop_hints)]
extern crate rustc_attr_ir;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path = "../../../src/entry_connector.rs"]
mod entry_connector;
#[path = "../../../src/mir_goto.rs"]
mod mir_goto;
#[path = "../../../src/synthetic_terminator.rs"]
mod synthetic_terminator;
use rustc_driver::{Callbacks, Compilation};
use rustc_middle::mir::{
    self, BasicBlock, BasicBlockData, Local, Place, Statement, StatementKind, StmtDebugInfo,
    TerminatorKind,
};
use rustc_middle::ty::TyCtxt;
use std::collections::BTreeSet;
fn same_statement<'tcx>(a: &Statement<'tcx>, b: &Statement<'tcx>) {
    assert_eq!(a.source_info, b.source_info, "statement origin");
    assert_eq!(a.kind, b.kind, "complete statement operation");
    assert_eq!(
        a.trust_modular_arith, b.trust_modular_arith,
        "arithmetic provenance"
    );
    assert_eq!(
        format!("{:?}", a.debuginfos),
        format!("{:?}", b.debuginfos),
        "ordered statement debug records"
    );
}
fn same_block<'tcx>(a: &BasicBlockData<'tcx>, b: &BasicBlockData<'tcx>) {
    assert_eq!(a.is_cleanup, b.is_cleanup, "block cleanup status");
    assert_eq!(a.statements.len(), b.statements.len(), "statement count");
    for (a, b) in a.statements.iter().zip(&b.statements) {
        same_statement(a, b);
    }
    assert_eq!(
        format!("{:?}", a.after_last_stmt_debuginfos),
        format!("{:?}", b.after_last_stmt_debuginfos),
        "ordered block-end debug records"
    );
    assert_eq!(
        a.terminator().source_info,
        b.terminator().source_info,
        "terminator origin"
    );
    assert_eq!(
        a.terminator().kind,
        b.terminator().kind,
        "complete original operation/hints"
    );
    #[cfg(rustc_terminator_attributes)]
    assert_eq!(
        format!("{:?}", a.terminator().attributes),
        format!("{:?}", b.terminator().attributes),
        "original global attributes"
    );
}
#[cfg(rustc_goto_loop_hints)]
fn hints() -> Vec<Vec<rustc_attr_ir::UnrollAttr>> {
    use rustc_attr_ir::UnrollAttr::{Count, Full, Hint, Never};
    vec![
        vec![],
        vec![Hint],
        vec![Full],
        vec![Never],
        vec![Count(0)],
        vec![Count(1)],
        vec![Count(7)],
        vec![Count(65535)],
        vec![Count(u32::MAX)],
        vec![Hint, Count(7)],
        vec![Count(7), Hint],
        vec![Never, Hint, Never, Count(u32::MAX)],
    ]
}
fn entry_kind<'tcx>(style: usize) -> TerminatorKind<'tcx> {
    #[cfg(rustc_goto_loop_hints)]
    {
        TerminatorKind::Goto {
            target: mir::START_BLOCK,
            loop_hint_attrs: hints()[style].iter().copied().collect(),
        }
    }
    #[cfg(not(rustc_goto_loop_hints))]
    {
        let _ = style;
        TerminatorKind::Goto {
            target: mir::START_BLOCK,
        }
    }
}
fn seed_debug(block: &mut BasicBlockData<'_>) {
    block
        .after_last_stmt_debuginfos
        .push(StmtDebugInfo::InvalidAssign(Local::from_u32(0)));
    for statement in &mut block.statements {
        statement.trust_modular_arith = true;
        statement
            .debuginfos
            .push(StmtDebugInfo::InvalidAssign(Local::from_u32(0)));
    }
    #[cfg(rustc_terminator_attributes)]
    block
        .terminator_mut()
        .attributes
        .push(rustc_hir::attrs::AttributeKind::Cold);
}
struct Audit;
impl Callbacks for Audit {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let mut functions = BTreeSet::new();
        let (mut terms, mut gotos, mut moved_real, mut moved_seeded) = (0, 0, 0, 0);
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
            for block in body.basic_blocks.iter() {
                let original = &block.terminator().kind;
                let before = original.clone();
                if let Some(goto) = mir_goto::view(original) {
                    assert!(std::ptr::eq(goto.original(), original));
                    assert_eq!(goto.original(), &before, "real complete Goto");
                    let TerminatorKind::Goto {
                        target,
                        #[cfg(rustc_goto_loop_hints)]
                        loop_hint_attrs,
                    } = original
                    else {
                        unreachable!()
                    };
                    #[cfg(rustc_goto_loop_hints)]
                    let _ = loop_hint_attrs;
                    assert_eq!(goto.target(), *target);
                    gotos += 1;
                } else {
                    assert!(!matches!(original, TerminatorKind::Goto { .. }));
                }
                assert_eq!(original, &before, "real read-only query");
                terms += 1;
            }
            let styles = if cfg!(rustc_goto_loop_hints) { 12 } else { 1 };
            for style in 0..=styles {
                let mut candidate = body.clone();
                let mut source = candidate.basic_blocks[mir::START_BLOCK]
                    .terminator()
                    .source_info;
                let mut assemble = candidate
                    .basic_blocks
                    .iter()
                    .flat_map(|b| &b.statements)
                    .next()
                    .cloned()
                    .unwrap_or_else(|| Statement::new(source, StatementKind::Nop));
                assemble
                    .debuginfos
                    .push(StmtDebugInfo::InvalidAssign(Local::from_u32(0)));
                assemble.trust_modular_arith = style > 0;
                let assemble_before = assemble.clone();
                if style > 0 {
                    source.scope = mir::SourceScope::from_u32(17);
                    let blocks = candidate.basic_blocks_mut();
                    blocks[mir::START_BLOCK].terminator_mut().source_info = source;
                    blocks[mir::START_BLOCK].terminator_mut().kind = entry_kind(style - 1);
                    seed_debug(&mut blocks[mir::START_BLOCK]);
                    blocks.push(BasicBlockData::new(
                        Some(synthetic_terminator::new(source, entry_kind(style - 1))),
                        false,
                    ));
                    blocks.push(BasicBlockData::new(
                        Some(synthetic_terminator::new(
                            source,
                            TerminatorKind::Drop {
                                place: tcx.mk_place_deref(Place::from(Local::from_u32(0))),
                                target: mir::START_BLOCK,
                                unwind: mir::UnwindAction::Cleanup(mir::START_BLOCK),
                                replace: true,
                                drop: Some(mir::START_BLOCK),
                            },
                        )),
                        true,
                    ));
                }
                let before = candidate.clone();
                let moved = BasicBlock::from_u32(before.basic_blocks.len() as u32);
                entry_connector::move_start(&mut candidate, assemble);
                assert_eq!(candidate.basic_blocks.len(), before.basic_blocks.len() + 1);
                for index in 0..before.basic_blocks.len() {
                    let bb = BasicBlock::from_u32(index as u32);
                    let mut expected = before.basic_blocks[bb].clone();
                    if style > 0 && index + 1 == before.basic_blocks.len() {
                        // Independent expected values for every seeded Drop edge.
                        let TerminatorKind::Drop {
                            place,
                            target,
                            unwind,
                            replace,
                            drop,
                        } = &before.basic_blocks[bb].terminator().kind
                        else {
                            unreachable!()
                        };
                        assert_eq!(*target, mir::START_BLOCK);
                        assert_eq!(*unwind, mir::UnwindAction::Cleanup(mir::START_BLOCK));
                        assert_eq!(*drop, Some(mir::START_BLOCK));
                        expected.terminator_mut().kind = TerminatorKind::Drop {
                            place: *place,
                            target: moved,
                            unwind: mir::UnwindAction::Cleanup(moved),
                            replace: *replace,
                            drop: Some(moved),
                        };
                    } else {
                        expected.terminator_mut().successors_mut(|target| {
                            if *target == mir::START_BLOCK {
                                *target = moved;
                            }
                        });
                    }
                    same_block(
                        &candidate.basic_blocks[if bb == mir::START_BLOCK { moved } else { bb }],
                        &expected,
                    );
                }
                let connector = &candidate.basic_blocks[mir::START_BLOCK];
                assert!(!connector.is_cleanup);
                assert_eq!(
                    connector.statements.len(),
                    1,
                    "fresh connector statement count"
                );
                same_statement(&connector.statements[0], &assemble_before);
                assert!(
                    connector.after_last_stmt_debuginfos.is_empty(),
                    "fresh connector has no old end debug records"
                );
                assert_eq!(
                    connector.terminator().source_info,
                    source,
                    "connector source origin"
                );
                assert_eq!(
                    mir_goto::view(&connector.terminator().kind)
                        .unwrap()
                        .target(),
                    moved,
                    "connector successor"
                );
                #[cfg(rustc_terminator_attributes)]
                assert!(
                    connector.terminator().attributes.is_empty(),
                    "fresh connector has no global attributes"
                );
                #[cfg(rustc_goto_loop_hints)]
                {
                    let TerminatorKind::Goto {
                        target: _,
                        loop_hint_attrs,
                    } = &connector.terminator().kind
                    else {
                        unreachable!()
                    };
                    assert!(
                        loop_hint_attrs.is_empty(),
                        "fresh connector has no old loop hints"
                    );
                }
                assert_eq!(candidate.arg_count, before.arg_count);
                assert_eq!(candidate.local_decls.len(), before.local_decls.len());
                assert_eq!(candidate.source, before.source);
                assert_eq!(candidate.span, before.span);
                if style == 0 {
                    moved_real += 1;
                } else {
                    moved_seeded += 1;
                }
            }
            assert!(functions.insert(name));
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
        assert!(gotos > 0);
        assert_eq!(moved_real, 8);
        assert_eq!(
            moved_seeded,
            if cfg!(rustc_goto_loop_hints) { 96 } else { 8 }
        );
        println!(
            "GOTO_REAL functions=8 terms={terms} gotos={gotos} real_entry_moves={moved_real} seeded_entry_moves={moved_seeded}"
        );
        Compilation::Stop
    }
}
fn main() {
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Audit);
}
