// trust-cg-verify/trust_ir_mid_tv_fillcall.rs - fill-call witness refusal
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The retained fill-call witness vocabulary supplies no helper authority.
//! A declaration's name and signature do not establish the body of an external
//! function: an ordinary host may implement it differently. Every nonempty
//! witness is therefore refused until a shared source-bound helper contract is
//! checked. No loop is invented for the interpreter differential.

use trust_ir::{BlockId, Function, Module, ValueId};

use super::{MidTvError, WitnessVerdict};

/// One proposed fill-helper call rewrite, with its source position and two
/// proposed fresh values. These fields do not authenticate the external helper.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FillCall {
    /// Source block of the proposed rewrite.
    pub block: BlockId,
    /// Source instruction position of the proposed rewrite.
    pub index: usize,
    /// Proposed byte-count result.
    pub count: ValueId,
    /// Proposed fill-byte result.
    pub byte: ValueId,
}

/// An untrusted fill-call rewrite proposal. Nonempty proposals currently refuse.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FillCallWitness {
    /// Proposed rewrites in source order.
    pub rewrites: Vec<FillCall>,
}

pub(super) fn rebuild_fill_call(
    _module: &Module,
    _pointer_bits: u32,
    source: &Function,
    witness: &FillCallWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    if let Some(rewrite) = witness.rewrites.first() {
        return Err(MidTvError::NotFillCall {
            block: rewrite.block,
            index: rewrite.index,
            why: "an external fill-helper declaration has no source-bound helper body or contract"
                .to_string(),
        });
    }
    Ok((
        source.clone(),
        WitnessVerdict {
            exact: 0,
            refinements: 0,
        },
    ))
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_fillcall_tests.rs"]
mod tests;
