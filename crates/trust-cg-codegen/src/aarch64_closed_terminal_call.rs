// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Paired terminal-call control check over an original TrustIR module and
//! actual Mach-O object and image bytes.

use trust_cg_verify::aarch64_closed_callee::{
    Aarch64ClosedCallText, CheckedAarch64ClosedControl, ClosedAarch64CallError,
    ResolvedClosedCalleeCall, check_aarch64_closed_control,
};
use trust_ir::{FuncId, Module};

use crate::macho::linked_image::{CheckedClosedCallPlacement, check_closed_call_placement};

#[derive(Debug, thiserror::Error)]
pub enum MachoClosedTerminalCallError {
    #[error("the selected source function identity is missing or ambiguous")]
    SourceIdentity,
    #[error("Mach-O caller, callee or branch custody refused: {0}")]
    Placement(String),
    #[error(transparent)]
    Control(#[from] ClosedAarch64CallError),
}

/// Borrowed exact endpoints of a paired terminal-call check. The caller's
/// immediate continuation cannot run by normal return on either side.
/// The check uses ordinary AAPCS64 calls and terminal BRK semantics. It does
/// not establish matching print/exit effects, certify other rows, or permit
/// execution or proof promotion.
#[derive(Debug)]
pub struct CheckedMachoClosedTerminalCall<'a> {
    control: CheckedAarch64ClosedControl<'a>,
    placement: CheckedClosedCallPlacement<'a>,
}

impl CheckedMachoClosedTerminalCall<'_> {
    pub fn control(&self) -> &CheckedAarch64ClosedControl<'_> {
        &self.control
    }

    pub fn placement(&self) -> &CheckedClosedCallPlacement<'_> {
        &self.placement
    }
}

pub fn check_macho_source_bound_terminal_call<'a>(
    module: &'a Module,
    caller: FuncId,
    callee: FuncId,
    object: &'a [u8],
    image: &'a [u8],
    call_offset: usize,
) -> Result<CheckedMachoClosedTerminalCall<'a>, MachoClosedTerminalCallError> {
    use MachoClosedTerminalCallError as Error;
    let name = |id| {
        let mut functions = module.functions.iter().filter(|function| function.id == id);
        let function = functions.next()?;
        functions.next().is_none().then_some(function.name.as_str())
    };
    let caller_symbol = format!("_{}", name(caller).ok_or(Error::SourceIdentity)?);
    let callee_symbol = format!("_{}", name(callee).ok_or(Error::SourceIdentity)?);
    let placement =
        check_closed_call_placement(object, image, &caller_symbol, &callee_symbol, call_offset)
            .map_err(Error::Placement)?;

    let calls = placement
        .callee_calls()
        .iter()
        .map(|call| {
            Some(ResolvedClosedCalleeCall {
                offset: call.offset(),
                symbol: call.symbol().strip_prefix('_')?,
                target: call.destination(),
            })
        })
        .collect::<Option<Vec<_>>>()
        .ok_or(Error::SourceIdentity)?;
    let control = check_aarch64_closed_control(
        module,
        caller,
        callee,
        &Aarch64ClosedCallText {
            caller: placement.caller_bytes(),
            caller_address: placement.caller_address(),
            callee: placement.callee_bytes(),
            callee_address: placement.callee_address(),
            call_offset: placement.call_offset(),
            callee_calls: &calls,
        },
    )?;
    Ok(CheckedMachoClosedTerminalCall { control, placement })
}
