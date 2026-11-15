// Copyright 2026 Andrew Yates | Apache-2.0
//! Representation questions after the containing module's refinement admission.

use crate::{adapter::AdapterError, types::Type};
use trust_ir::{Module, Ty};

/// A type whose single refinement layer has been resolved in module context.
/// Keep source `Ty`s on proof and implication paths; machine category decisions
/// use this carrier. Module entry points validate refinements before constructing
/// it. A table-only adapter cannot resolve a refinement through this constructor.
#[derive(Clone, Copy)]
pub(crate) struct ReprTy<'a>(&'a Ty);

impl<'a> ReprTy<'a> {
    pub(crate) fn for_module(module: Option<&'a Module>, ty: &'a Ty) -> Result<Self, AdapterError> {
        let representation = match ty {
            Ty::Refine(base, _) => {
                let module = module.ok_or_else(|| AdapterError::InvalidRefinement(
                    "Ty::Refine requires its validated containing Module for representation decisions".into(),
                ))?;
                let representation = module.representation_ty(ty).ok_or_else(|| {
                    AdapterError::InvalidRefinement(format!(
                        "Refine({base:?}, _) has an out-of-range representation type"
                    ))
                })?;
                if matches!(representation, Ty::Refine(..)) {
                    return Err(AdapterError::InvalidRefinement(
                        "nested or cyclic refinements have no admitted representation".into(),
                    ));
                }
                representation
            }
            other => other,
        };
        Ok(Self(representation))
    }

    pub(crate) fn ty(self) -> &'a Ty {
        self.0
    }

    pub(crate) fn narrow_extension(self) -> Option<(Type, bool)> {
        match self.0 {
            Ty::I8 => Some((Type::I8, true)),
            Ty::U8 => Some((Type::I8, false)),
            Ty::I16 => Some((Type::I16, true)),
            Ty::U16 => Some((Type::I16, false)),
            _ => None,
        }
    }

    pub(crate) fn is_signed_integer(self) -> bool {
        matches!(
            self.0,
            Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128 | Ty::Isize
        )
    }

    pub(crate) fn is_i128(self) -> bool {
        matches!(self.0, Ty::I128 | Ty::U128)
    }
}
