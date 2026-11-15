// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Read-only Goto projections and fresh MIR connectors.
//!
//! A view borrows the complete original operation. Asking for its successor
//! does not consume, reconstruct or remove ordered loop hints. Emission must
//! still handle that original descriptor's metadata; this is not a lowering.

use rustc_middle::mir::{BasicBlock, TerminatorKind};

#[derive(Clone, Copy)]
pub(super) struct View<'a, 'tcx> {
    original: &'a TerminatorKind<'tcx>,
}

impl<'a, 'tcx> View<'a, 'tcx> {
    pub(super) fn original(self) -> &'a TerminatorKind<'tcx> {
        self.original
    }

    pub(super) fn target(self) -> BasicBlock {
        let TerminatorKind::Goto {
            target,
            #[cfg(rustc_goto_loop_hints)]
            loop_hint_attrs,
        } = self.original()
        else {
            unreachable!("Goto view is created only from a Goto")
        };
        // A target-only CFG query keeps the original payload borrowed intact.
        #[cfg(rustc_goto_loop_hints)]
        let _ = loop_hint_attrs;
        *target
    }
}

pub(super) fn view<'a, 'tcx>(kind: &'a TerminatorKind<'tcx>) -> Option<View<'a, 'tcx>> {
    match kind {
        TerminatorKind::Goto {
            target,
            #[cfg(rustc_goto_loop_hints)]
            loop_hint_attrs,
        } => {
            let _ = target;
            #[cfg(rustc_goto_loop_hints)]
            let _ = loop_hint_attrs;
            Some(View { original: kind })
        }
        _ => None,
    }
}

/// A new connector has no loop hint belonging to a prior operation.
pub(super) fn new<'tcx>(target: BasicBlock) -> TerminatorKind<'tcx> {
    TerminatorKind::Goto {
        target,
        #[cfg(rustc_goto_loop_hints)]
        loop_hint_attrs: Default::default(),
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use rustc_middle::mir::{Local, Place, UnwindAction, UnwindTerminateReason};

    #[cfg(rustc_goto_loop_hints)]
    pub(crate) fn hint_vectors() -> Vec<Vec<rustc_attr_ir::UnrollAttr>> {
        use rustc_attr_ir::UnrollAttr::{Count, Full, Hint, Never};
        let mut values = vec![vec![], vec![Hint], vec![Full], vec![Never]];
        for count in [0, 1, 7, 65535, u32::MAX] {
            values.push(vec![Count(count)]);
        }
        values.extend([
            vec![Hint, Count(7)],
            vec![Count(7), Hint],
            vec![Never, Hint, Never, Count(u32::MAX)],
        ]);
        assert_eq!(values.len(), 12);
        values
    }

    #[test]
    fn fresh_connectors_preserve_the_target_and_start_without_loop_hints() {
        let mut cases = 0;
        for index in [0, 1, 7, 65535] {
            let target = BasicBlock::from_u32(index);
            let actual = new(target);
            let projected = view(&actual).expect("fresh Goto kind");
            assert_eq!(projected.target(), target, "fresh Goto target");
            assert!(std::ptr::eq(projected.original(), &actual));
            #[cfg(rustc_goto_loop_hints)]
            {
                let TerminatorKind::Goto {
                    target: _,
                    loop_hint_attrs,
                } = &actual
                else {
                    unreachable!()
                };
                assert!(
                    loop_hint_attrs.is_empty(),
                    "fresh connector has no loop hint"
                );
            }
            cases += 1;
        }
        assert_eq!(cases, 4);
        println!("GOTO_FRESH cases={cases}");
    }

    #[test]
    fn successor_queries_borrow_the_complete_original_operation() {
        let mut cases = 0;
        for index in [0, 1, 7, 65535] {
            let target = BasicBlock::from_u32(index);
            #[cfg(rustc_goto_loop_hints)]
            let kinds: Vec<_> = hint_vectors()
                .into_iter()
                .map(|hints| TerminatorKind::Goto {
                    target,
                    loop_hint_attrs: hints.into_iter().collect(),
                })
                .collect();
            #[cfg(not(rustc_goto_loop_hints))]
            let kinds = [TerminatorKind::Goto { target }];
            for original in kinds {
                let before = original.clone();
                let projected = view(&original).expect("original Goto kind");
                assert_eq!(projected.target(), target, "original successor");
                assert!(
                    std::ptr::eq(projected.original(), &original),
                    "same original descriptor"
                );
                assert_eq!(
                    projected.original(),
                    &before,
                    "complete ordered hint payload"
                );
                assert_eq!(original, before, "read-only query changes no operation");
                cases += 1;
            }
        }
        assert_eq!(cases, if cfg!(rustc_goto_loop_hints) { 48 } else { 4 });
        println!("GOTO_BORROW cases={cases}");
    }

    #[test]
    fn other_operations_never_acquire_a_goto_view() {
        let mut kinds = vec![
            TerminatorKind::Return,
            TerminatorKind::Unreachable,
            TerminatorKind::UnwindResume,
        ];
        for target in [1, 7] {
            for unwind in [
                UnwindAction::Continue,
                UnwindAction::Unreachable,
                UnwindAction::Cleanup(BasicBlock::from_u32(13)),
                UnwindAction::Terminate(UnwindTerminateReason::Abi),
                UnwindAction::Terminate(UnwindTerminateReason::InCleanup),
            ] {
                kinds.push(TerminatorKind::Drop {
                    place: Place::from(Local::from_u32(1)),
                    target: BasicBlock::from_u32(target),
                    unwind,
                    replace: target == 7,
                    drop: Some(BasicBlock::from_u32(23)),
                });
            }
        }
        let mut cases = 0;
        for original in kinds {
            let before = original.clone();
            assert!(view(&original).is_none(), "non-Goto operation");
            assert_eq!(original, before, "non-Goto payload stays intact");
            cases += 1;
        }
        assert_eq!(cases, 13);
        println!("GOTO_REJECT cases={cases}");
    }
}
