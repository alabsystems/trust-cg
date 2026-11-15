//! Reviewed compiler representation changes; no proof authority.
// Author: Andrew Yates | Copyright 2026 | License: Apache-2.0

use rustc_middle::ty::TyCtxt;

/// Ask only for allocation provenance, without casting plain scalar bits.
/// New rustc's infallible to_pointer panics on a non-pointer-width integer;
/// older rustc returned an interpreter error for the same input. Integer
/// addresses have no allocation provenance and belong to the integer paths.
pub(super) fn allocation_pointer(
    tcx: TyCtxt<'_>,
    scalar: rustc_middle::mir::interpret::Scalar,
) -> Option<rustc_middle::mir::interpret::Pointer<rustc_middle::mir::interpret::CtfeProvenance>> {
    if scalar.try_to_scalar_int().is_ok() {
        return None;
    }
    // This conversion has its own measured capability: the session API does
    // not decide whether to_pointer returns a fallible result or a pointer.
    crate::constant_pointer::checked(&tcx, scalar)?
        .into_pointer_or_addr()
        .ok()
}

/// Refuse new operations whose extra validity has no lowering obligation yet,
/// before dead-local/interception shortcuts or MIR rewrites can erase them.
pub(super) fn refuse_unmodeled_body(body: &rustc_middle::mir::Body<'_>) -> Result<(), String> {
    #[cfg(rustc_session_split)]
    {
        use rustc_middle::mir::visit::{PlaceContext, Visitor};
        use rustc_middle::mir::{Location, Place, ProjectionElem, Rvalue};
        struct Check {
            refusal: Option<String>,
        }
        impl<'tcx> Visitor<'tcx> for Check {
            fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
                if matches!(
                    rvalue,
                    Rvalue::Cast(rustc_middle::mir::CastKind::BoxDerefTransmute, ..)
                ) {
                    self.refusal = Some("[TCG-BOX-DEREF] BoxDerefTransmute requires an unmodeled Box validity obligation".to_owned());
                }
                self.super_rvalue(rvalue, location);
            }
            fn visit_place(
                &mut self,
                place: &Place<'tcx>,
                context: PlaceContext,
                location: Location,
            ) {
                if place
                    .projection
                    .iter()
                    .any(|elem| matches!(elem, ProjectionElem::PhantomDeref))
                {
                    self.refusal = Some(
                        "[TCG-PROJECTION] borrow-checker PhantomDeref has no runtime address model"
                            .to_owned(),
                    );
                }
                self.super_place(place, context, location);
            }
        }
        let mut check = Check { refusal: None };
        check.visit_body(body);
        if let Some(refusal) = check.refusal {
            return Err(refusal);
        }
    }
    #[cfg(not(rustc_session_split))]
    let _ = body;
    Ok(())
}
