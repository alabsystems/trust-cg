// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! A scalar pair in ABI memory order. The modern representation supplies the
//! second offset explicitly. Only the legacy tuple representation derives it
//! from the scalars' sizes and default ABI alignment.

use rustc_abi::{BackendRepr, HasDataLayout, Scalar, Size};

#[derive(Clone, Copy, Debug)]
pub(super) struct Pair {
    pub(super) a: Scalar,
    pub(super) b: Scalar,
    #[cfg(rustc_scalar_pair_struct)]
    b_offset: Size,
}

impl Pair {
    pub(super) fn second_offset<C: HasDataLayout>(self, cx: &C) -> Size {
        #[cfg(rustc_scalar_pair_struct)]
        {
            let _ = cx;
            self.b_offset
        }
        #[cfg(not(rustc_scalar_pair_struct))]
        {
            self.a.size(cx).align_to(self.b.default_align(cx).abi)
        }
    }
}

pub(super) fn view(repr: BackendRepr) -> Option<Pair> {
    match repr {
        #[cfg(rustc_scalar_pair_struct)]
        BackendRepr::ScalarPair { a, b, b_offset } => Some(Pair { a, b, b_offset }),
        #[cfg(not(rustc_scalar_pair_struct))]
        BackendRepr::ScalarPair(a, b) => Some(Pair { a, b }),
        _ => None,
    }
}

/// Existing unit fixtures describe the canonical legacy geometry. Construct
/// that same test input on either API; production consumers only read `view`.
#[cfg(test)]
pub(super) fn canonical<C: HasDataLayout>(a: Scalar, b: Scalar, cx: &C) -> BackendRepr {
    #[cfg(rustc_scalar_pair_struct)]
    {
        // Every compiler with the struct spelling returns the ABI alignment
        // itself from `default_align`; the tuple spelling's `.abi` projection
        // does not exist there.
        let b_offset = a.size(cx).align_to(b.default_align(cx));
        BackendRepr::ScalarPair { a, b, b_offset }
    }
    #[cfg(not(rustc_scalar_pair_struct))]
    {
        let _ = cx;
        BackendRepr::ScalarPair(a, b)
    }
}
