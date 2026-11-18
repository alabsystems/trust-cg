// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Check a terminal call under ordinary AAPCS64 control flow. An inner call
//! may stop the activation or resume at its own BL+4. The checked callee has
//! no normal return on either path. The scope excludes unwinding, nonlocal
//! transfers, resumption after BRK and modification of the checked text.

use trust_ir::{BlockId, FuncId, Module, proof::ProofDigest};

use crate::aarch64_control_decode::{A64ControlWord, decode_a64_control_word};
use crate::aarch64_instruction_word_proofs::{DecodedWord, decode_word};
use crate::aarch64_trap_expansion::{Word as TrapWord, decode as decode_trap};

#[path = "../../../formal/lean/Trust/A64/ClosedCallee.lean"]
clean mod closed_callee;

#[path = "aarch64_closed_call_source.rs"]
mod source;

#[derive(Debug, thiserror::Error)]
pub enum ClosedAarch64CallError {
    #[error("the original source does not have the selected closed call and trap")]
    Source,
    #[error("the linked function extents or terminal call offset are invalid")]
    Extent,
    #[error("the terminal BL does not reach the selected callee entry")]
    CallTarget,
    #[error("the caller's actual control flow is unsupported at byte {0:#x}")]
    CallerControl(usize),
    #[error("the callee's actual control flow is unsupported at byte {0:#x}")]
    CalleeControl(usize),
    #[error("the callee's direct calls differ from the original binding")]
    CalleeCalls,
}

/// A resolved direct call in the callee, with a source-spelled symbol and an
/// offset relative to its entry. The object/link owner supplies the binding.
#[derive(Debug)]
pub struct ResolvedClosedCalleeCall<'a> {
    pub offset: usize,
    pub symbol: &'a str,
    pub target: u64,
}

/// Exact linked text slices and the selected caller BL offset.
pub struct Aarch64ClosedCallText<'a> {
    pub caller: &'a [u8],
    pub caller_address: u64,
    pub callee: &'a [u8],
    pub callee_address: u64,
    pub call_offset: usize,
    pub callee_calls: &'a [ResolvedClosedCalleeCall<'a>],
}

/// The two checked control-flow endpoints. This result concerns reachability
/// of the caller's normal continuation. It carries no permission to install
/// the image or to credit the callee's memory, arithmetic or output effects.
#[derive(Debug)]
pub struct CheckedAarch64ClosedControl<'a> {
    source: source::CheckedClosedSourceCall<'a>,
    call_offset: usize,
    callee_words: usize,
}

impl CheckedAarch64ClosedControl<'_> {
    pub fn caller_name(&self) -> &str {
        self.source.caller_name()
    }

    pub fn callee_name(&self) -> &str {
        self.source.callee_name()
    }

    pub fn call_offset(&self) -> usize {
        self.call_offset
    }

    pub fn caller_terminal_site(&self) -> (BlockId, usize, usize) {
        self.source.caller_terminal_site()
    }

    pub fn source_digest(&self) -> ProofDigest {
        self.source.module_body_digest()
    }

    pub fn callee_call_count(&self) -> usize {
        self.source.callee_call_count()
    }

    pub fn callee_words(&self) -> usize {
        self.callee_words
    }
}

const FALLTHROUGH: u32 = 0;
const DIRECT_CALL: u32 = 1;
const TERMINAL_TRAP: u32 = 2;

pub fn check_aarch64_closed_control<'a>(
    module: &'a Module,
    caller: FuncId,
    callee: FuncId,
    text: &Aarch64ClosedCallText<'_>,
) -> Result<CheckedAarch64ClosedControl<'a>, ClosedAarch64CallError> {
    let source = source::bind(module, caller, callee).ok_or(ClosedAarch64CallError::Source)?;
    check_linked_control(text, source.callee_calls())?;
    Ok(CheckedAarch64ClosedControl {
        source,
        call_offset: text.call_offset,
        callee_words: text.callee.len() / 4,
    })
}

fn extent(address: u64, bytes: &[u8]) -> Option<std::ops::Range<u64>> {
    if !address.is_multiple_of(4)
        || bytes.is_empty()
        || i64::try_from(bytes.len()).is_err()
        || !bytes.len().is_multiple_of(4)
    {
        return None;
    }
    Some(address..address.checked_add(u64::try_from(bytes.len()).ok()?)?)
}

fn call_target(word: u32, pc: u64) -> Option<u64> {
    let DecodedWord::BranchImm { op: 1, imm26 } = decode_word(word)? else {
        return None;
    };
    let displacement = ((imm26 as i32) << 6) >> 6;
    pc.checked_add_signed(i64::from(displacement) * 4)
}

fn is_terminal_trap(word: u32) -> bool {
    matches!(decode_trap(word), Ok(TrapWord::Brk { imm16: 1 }))
}

fn words(bytes: &[u8]) -> impl Iterator<Item = (usize, u32)> + '_ {
    bytes
        .chunks_exact(4)
        .enumerate()
        .map(|(i, word)| (i * 4, u32::from_le_bytes(word.try_into().unwrap())))
}

fn check_linked_control(
    text: &Aarch64ClosedCallText<'_>,
    source_calls: &[&str],
) -> Result<(), ClosedAarch64CallError> {
    use ClosedAarch64CallError as Error;

    let caller = extent(text.caller_address, text.caller).ok_or(Error::Extent)?;
    let callee = extent(text.callee_address, text.callee).ok_or(Error::Extent)?;
    if caller.start < callee.end && callee.start < caller.end
        || text.call_offset.checked_add(8) != Some(text.caller.len())
    {
        return Err(Error::Extent);
    }
    let trap_offset = text.call_offset + 4;
    for (offset, word) in words(text.caller) {
        if offset == text.call_offset {
            if call_target(word, caller.start + offset as u64) != Some(callee.start) {
                return Err(Error::CallTarget);
            }
        } else if offset == trap_offset {
            if !is_terminal_trap(word) {
                return Err(Error::CallerControl(offset));
            }
        } else if let Some(control) = decode_a64_control_word(word) {
            let displacement = match control {
                A64ControlWord::Branch { displacement }
                | A64ControlWord::ConditionalBranch { displacement, .. }
                | A64ControlWord::CompareBranch { displacement, .. } => displacement,
                A64ControlWord::Return { .. } => return Err(Error::CallerControl(offset)),
            };
            let destination = (offset as i64)
                .checked_add(displacement * 4)
                .ok_or(Error::CallerControl(offset))?;
            if !(0..trap_offset as i64).contains(&destination) {
                return Err(Error::CallerControl(offset));
            }
        } else if !caller_fallthrough(word) {
            return Err(Error::CallerControl(offset));
        }
    }

    if text.callee_calls.len() != source_calls.len() || source_calls.is_empty() {
        return Err(Error::CalleeCalls);
    }
    let mut bindings = text.callee_calls.iter().zip(source_calls);
    for (offset, word) in words(text.callee) {
        let kind = if let Some(target) = call_target(word, callee.start + offset as u64) {
            let (binding, symbol) = bindings.next().ok_or(Error::CalleeCalls)?;
            if caller.contains(&target)
                || callee.contains(&target)
                || binding.offset != offset
                || binding.target != target
                || binding.symbol != *symbol
            {
                return Err(Error::CalleeCalls);
            }
            DIRECT_CALL
        } else if is_terminal_trap(word) {
            TERMINAL_TRAP
        } else if callee_fallthrough(word) {
            FALLTHROUGH
        } else {
            return Err(Error::CalleeControl(offset));
        };
        if trust_cg_a64_closed_callee_row(kind, u32::from(offset + 4 == text.callee.len())) != 1 {
            return Err(Error::CalleeControl(offset));
        }
    }
    if bindings.next().is_some() {
        return Err(Error::CalleeCalls);
    }
    Ok(())
}

fn callee_fallthrough(word: u32) -> bool {
    if matches!(
        decode_word(word),
        Some(
            DecodedWord::AddSubImm { sf: 1, s: 0, .. }
                | DecodedWord::AddSubShifted {
                    sf: 1,
                    op: 0,
                    s: 0,
                    shift: 0,
                    ..
                }
                | DecodedWord::LogicalShifted {
                    opc: 1,
                    shift: 0,
                    n: 0,
                    imm6: 0,
                    rn: 31,
                    ..
                }
                | DecodedWord::MoveWide {
                    sf: 1,
                    opc: 2 | 3,
                    ..
                }
                | DecodedWord::LoadStoreUnsigned {
                    size: 3,
                    v: 0,
                    opc: 0 | 1,
                    ..
                }
                | DecodedWord::Dp3 {
                    sf: 1,
                    op54: 0,
                    op31: 6,
                    o0: 0,
                    ra: 31,
                    ..
                }
                | DecodedWord::Dp3 {
                    sf: 0,
                    op54: 0,
                    op31: 0,
                    o0: 1,
                    ..
                }
        )
    ) {
        return true;
    }

    // ADRP (immlo splits around the fixed field) and LSR X, the UBFM alias
    // with N=1 and imms=63.
    if word & 0x9f00_0000 == 0x9000_0000 || word & 0xffc0_fc00 == 0xd340_fc00 {
        return true;
    }
    match word & 0xffc0_0000 {
        0xa900_0000 => true, // STP X, signed offset
        0xa980_0000 => {
            // STP X, pre-indexed; exclude writeback overlap with a GPR.
            let base = (word >> 5) & 31;
            base == 31 || (base != word & 31 && base != (word >> 10) & 31)
        }
        _ => false,
    }
}

fn caller_fallthrough(word: u32) -> bool {
    callee_fallthrough(word)
        || matches!(
            decode_word(word),
            Some(
                DecodedWord::AddSubShifted { sf: 1, op: 1, s: 1, shift: 0, rd: 31, .. }
                    | DecodedWord::Dp3 { sf: 1, op54: 0, op31: 0, .. }
            )
        )
        || word & 0xffe0_fc00 == 0x9ac0_0800 // UDIV X
        || word & 0xffff_fc00 == 0xb240_0000 // ORR X, #1
}

#[cfg(test)]
#[path = "aarch64_closed_callee_tests.rs"]
mod tests;
