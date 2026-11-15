// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Construct synthetic operations with their original source and complete kind.
//! Existing terminators must be cloned/retargeted when their attributes belong
//! to the operation. This factory matches callers that deliberately start with
//! empty top-level attributes; metadata inside `kind` is forwarded unchanged.

use rustc_middle::mir::{SourceInfo, Terminator, TerminatorKind};

pub(super) fn new<'tcx>(source_info: SourceInfo, kind: TerminatorKind<'tcx>) -> Terminator<'tcx> {
    Terminator {
        source_info,
        kind,
        #[cfg(rustc_terminator_attributes)]
        attributes: Default::default(),
    }
}

#[cfg(test)]
mod tests {
    use crate::synthetic_terminator;
    use rustc_middle::mir::{
        BasicBlock, Local, Place, SourceInfo, SourceScope, TerminatorKind, UnwindAction,
        UnwindTerminateReason,
    };
    use rustc_span::{BytePos, Span, create_default_session_globals_then};

    fn origins() -> Vec<SourceInfo> {
        let mut values = Vec::new();
        for scope in [0, 2, 17] {
            for (lo, hi) in [(1, 3), (7, 31), (65535, 65541)] {
                values.push(SourceInfo {
                    span: Span::with_root_ctxt(BytePos(lo), BytePos(hi)),
                    scope: SourceScope::from_u32(scope),
                });
            }
        }
        values
    }

    #[test]
    fn source_origin_and_complete_simple_kinds_are_preserved() {
        create_default_session_globals_then(|| {
            let mut cases = 0;
            for source in origins() {
                for kind in [
                    TerminatorKind::Return,
                    TerminatorKind::Unreachable,
                    TerminatorKind::UnwindResume,
                ] {
                    let result = synthetic_terminator::new(source, kind.clone());
                    assert_eq!(result.source_info, source, "complete source origin");
                    assert_eq!(result.kind, kind, "complete supplied operation");
                    cases += 1;
                }
            }
            assert_eq!(cases, 27);
            println!("SYNTHETIC_TERM_ORIGIN cases={cases}");
        });
    }

    #[test]
    fn complete_drop_payload_and_unwind_actions_are_preserved() {
        create_default_session_globals_then(|| {
            let mut cases = 0;
            for source in origins() {
                for local in [1, 2, 17] {
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
                                        place: Place::from(Local::from_u32(local)),
                                        target: BasicBlock::from_u32(target),
                                        unwind,
                                        replace,
                                        drop: drop.map(BasicBlock::from_u32),
                                    };
                                    let result = synthetic_terminator::new(source, kind.clone());
                                    assert_eq!(result.source_info, source, "drop origin");
                                    assert_eq!(result.kind, kind, "all drop fields");
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
            assert_eq!(cases, 1620);
            println!("SYNTHETIC_TERM_DROP cases={cases}");
        });
    }

    #[test]
    fn synthetic_replacement_matches_the_existing_empty_attribute_policy() {
        create_default_session_globals_then(|| {
            let mut cases = 0;
            for source in origins() {
                for (style, previous) in [
                    TerminatorKind::Return,
                    TerminatorKind::Unreachable,
                    TerminatorKind::UnwindResume,
                ]
                .into_iter()
                .enumerate()
                {
                    let original = synthetic_terminator::new(source, previous);
                    #[cfg(rustc_terminator_attributes)]
                    let original = {
                        let mut original = original;
                        for _ in 0..style {
                            original
                                .attributes
                                .push(rustc_hir::attrs::AttributeKind::Cold);
                        }
                        original
                    };
                    let _ = style;
                    let mut expected = original.clone();
                    expected.kind = TerminatorKind::Return;
                    #[cfg(rustc_terminator_attributes)]
                    expected.attributes.clear();
                    let actual =
                        synthetic_terminator::new(original.source_info, TerminatorKind::Return);
                    assert_eq!(actual.source_info, expected.source_info);
                    assert_eq!(actual.kind, expected.kind);
                    #[cfg(rustc_terminator_attributes)]
                    assert!(
                        actual.attributes.is_empty(),
                        "synthetic attributes stay empty"
                    );
                    cases += 1;
                }
            }
            assert_eq!(cases, 27);
            println!(
                "SYNTHETIC_TERM_POLICY cases={cases} global_attributes={}",
                cfg!(rustc_terminator_attributes)
            );
        });
    }
}
