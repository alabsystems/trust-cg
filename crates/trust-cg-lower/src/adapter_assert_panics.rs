// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Source `Assert` is a panic, not this backend's internal checked-trap guard.
//! Native sited delivery is implemented in `adapter_sited_assert`. Unsited
//! checks still lack the runtime entry/location and fail closed on this floor.

use super::{AdapterError, Inst, TrustIrFunction};
use trust_ir::AssertKind;

pub(super) fn function_floor(function: &TrustIrFunction) -> Result<(), AdapterError> {
    for block in &function.blocks {
        for (inst_index, node) in block.body.iter().enumerate() {
            let location = || {
                format!(
                    "function `{}` bb{} instruction {}",
                    function.name,
                    block.id.index(),
                    inst_index
                )
            };
            let kind = match &node.inst {
                Inst::Assert {
                    cond: _,
                    kind,
                    site: Some(_),
                }
                | Inst::AssertInvoke {
                    cond: _,
                    kind,
                    site: _,
                    normal_dest: _,
                    normal_args: _,
                    unwind_dest: _,
                } => {
                    if kind.is_unspecified() {
                        return Err(unsupported(*kind, location()));
                    }
                    continue;
                }
                Inst::Assert {
                    cond: _,
                    kind,
                    site: None,
                } => kind,
                _ => continue,
            };
            if kind.is_unspecified() {
                let error = trust_ir_build::ValidationError::AssertPanicKindUnspecified {
                    function: function.name.clone(),
                    block: block.id.index(),
                    inst_index: inst_index as u32,
                };
                return Err(AdapterError::TrustIrAdmissionRefused {
                    error: error.to_string(),
                });
            }
            return Err(unsupported(*kind, location()));
        }
    }
    Ok(())
}

/// Exhaustive classification is also the pin-move fence for a new panic kind.
/// Unsited forms lack the entry/location needed for runtime delivery. An
/// ordinary trap has neither the panic message nor its hook/cleanup.
pub(super) fn unsupported(kind: AssertKind, location: String) -> AdapterError {
    let required_runtime = match kind {
        AssertKind::Unspecified => "unknown panic identity (no Rust entry point)",
        AssertKind::Overflow(_) => "the exact arithmetic-overflow panic entry point",
        AssertKind::DivByZero => "panic_const_div_by_zero",
        AssertKind::RemByZero => "panic_const_rem_by_zero",
        AssertKind::BoundsCheck { index: _, len: _ } => "panic_bounds_check(index, len)",
        AssertKind::MisalignedPtr {
            required: _,
            found: _,
        } => "panic_misaligned_pointer_dereference(required, found)",
        AssertKind::NullPtr => "panic_null_pointer_dereference",
    };
    AdapterError::AssertPanicUnsupported {
        location,
        kind,
        required_runtime,
    }
}
