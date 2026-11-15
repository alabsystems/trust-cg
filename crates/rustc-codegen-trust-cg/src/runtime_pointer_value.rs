//! Select a defined thin-pointer value without inventing an entry value ID.
//! These bindings establish storage/definedness, not allocation or drop origin.

use trust_ir::{Ty, ValueId};

pub(super) fn is_thin_pointer(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

pub(super) struct Bindings<'a> {
    pub cell: Option<(ValueId, &'a Ty)>,
    pub scalar: Option<ValueId>,
    pub entry: Option<(ValueId, &'a Ty)>,
    pub untouched_entry: bool,
    pub placeholder: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub(super) enum Source {
    Cell(ValueId),
    Value(ValueId),
}

/// A cell is authoritative even when an older scalar binding exists. Entry
/// fallback requires a recorded actual definition of the exact whole-local
/// type and a source local never rebound by this body. The ordinary final SSA
/// and type gates remain responsible for validating live scalar bindings.
pub(super) fn select(expected: &Ty, bindings: Bindings<'_>) -> Result<Source, &'static str> {
    if !is_thin_pointer(expected) {
        return Err("source local is not a thin pointer scalar");
    }
    if bindings.placeholder {
        return Err("placeholder borrow has no runtime pointer value");
    }
    if let Some((address, allocated)) = bindings.cell {
        if allocated != expected || !is_thin_pointer(allocated) {
            return Err("live cell type does not match the source pointer scalar");
        }
        return Ok(Source::Cell(address));
    }
    if let Some(value) = bindings.scalar {
        return Ok(Source::Value(value));
    }
    if let (true, Some((value, declared))) = (bindings.untouched_entry, bindings.entry) {
        if declared != expected {
            return Err("recorded entry definition has a different whole-local type");
        }
        return Ok(Source::Value(value));
    }
    Err("source pointer has no live binding or recorded untouched entry definition")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bindings<'a>() -> Bindings<'a> {
        Bindings {
            cell: None,
            scalar: None,
            entry: None,
            untouched_entry: false,
            placeholder: false,
        }
    }

    #[test]
    fn absence_never_manufactures_a_local_number_value() {
        assert!(select(&Ty::Ptr, bindings()).is_err());
        assert!(
            select(
                &Ty::Ptr,
                Bindings {
                    untouched_entry: true,
                    ..bindings()
                }
            )
            .is_err()
        );
    }

    #[test]
    fn cell_wins_over_a_stale_scalar_and_entry() {
        let pointer = Ty::Ptr;
        assert_eq!(
            select(
                &pointer,
                Bindings {
                    cell: Some((ValueId::new(31), &pointer)),
                    scalar: Some(ValueId::new(7)),
                    entry: Some((ValueId::new(2), &pointer)),
                    untouched_entry: true,
                    ..bindings()
                }
            ),
            Ok(Source::Cell(ValueId::new(31)))
        );
    }

    #[test]
    fn bad_cell_refuses_instead_of_using_an_old_binding() {
        let integer = Ty::I64;
        assert!(
            select(
                &Ty::Ptr,
                Bindings {
                    cell: Some((ValueId::new(31), &integer)),
                    scalar: Some(ValueId::new(7)),
                    ..bindings()
                }
            )
            .is_err()
        );
    }

    #[test]
    fn entry_requires_exact_type_and_untouched_source_local() {
        let pointer = Ty::Ptr;
        let mut facts = bindings();
        facts.entry = Some((ValueId::new(91), &pointer));
        assert!(select(&pointer, facts).is_err());
        assert_eq!(
            select(
                &pointer,
                Bindings {
                    entry: Some((ValueId::new(91), &pointer)),
                    untouched_entry: true,
                    ..bindings()
                }
            ),
            Ok(Source::Value(ValueId::new(91)))
        );
        let integer = Ty::I64;
        assert!(
            select(
                &pointer,
                Bindings {
                    entry: Some((ValueId::new(91), &integer)),
                    untouched_entry: true,
                    ..bindings()
                }
            )
            .is_err()
        );
    }

    #[test]
    fn nonpointer_and_placeholder_refuse_even_with_bindings() {
        let pointer = Ty::Ptr;
        assert!(
            select(
                &Ty::I64,
                Bindings {
                    scalar: Some(ValueId::new(7)),
                    ..bindings()
                }
            )
            .is_err()
        );
        assert!(
            select(
                &pointer,
                Bindings {
                    cell: Some((ValueId::new(31), &pointer)),
                    scalar: Some(ValueId::new(7)),
                    placeholder: true,
                    ..bindings()
                }
            )
            .is_err()
        );
    }

    #[test]
    fn live_scalar_does_not_require_entry_authority() {
        assert_eq!(
            select(
                &Ty::Ptr,
                Bindings {
                    scalar: Some(ValueId::new(73)),
                    ..bindings()
                }
            ),
            Ok(Source::Value(ValueId::new(73)))
        );
    }

    #[test]
    fn different_pointer_pointees_do_not_authorize_a_cell_or_entry() {
        let expected = Ty::PtrConst(Box::new(Ty::I64));
        let other = Ty::PtrConst(Box::new(Ty::I8));
        assert!(
            select(
                &expected,
                Bindings {
                    cell: Some((ValueId::new(31), &other)),
                    scalar: Some(ValueId::new(7)),
                    ..bindings()
                }
            )
            .is_err()
        );
        assert!(
            select(
                &expected,
                Bindings {
                    entry: Some((ValueId::new(91), &other)),
                    untouched_entry: true,
                    ..bindings()
                }
            )
            .is_err()
        );
    }

    #[test]
    fn ignored_and_expanded_whole_locals_cannot_be_pointer_values() {
        for whole in [Ty::Unit, Ty::Tuple(vec![Ty::Ptr, Ty::I64])] {
            assert!(
                select(
                    &whole,
                    Bindings {
                        scalar: Some(ValueId::new(7)),
                        entry: Some((ValueId::new(91), &Ty::Ptr)),
                        untouched_entry: true,
                        ..bindings()
                    }
                )
                .is_err()
            );
        }
    }
}
