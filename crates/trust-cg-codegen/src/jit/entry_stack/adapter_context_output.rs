// Copyright 2026 Andrew Yates | Apache-2.0
//! Fixed two-pointer/void host-stack adapter. Its target is supplied only by
//! the sealed installed Core entry consumer; this module grants no callability.

use super::{EntryStackError, HostContext};

std::arch::global_asm!(
    ".text",
    ".p2align 2",
    ".globl _trust_cg_owned_stack_context_output",
    ".private_extern _trust_cg_owned_stack_context_output",
    "_trust_cg_owned_stack_context_output:",
    "mov x9, sp",
    "str x9, [x1]",
    "mov x16, x0",
    "mov sp, x2",
    "stp x29, x30, [sp]",
    "str x1, [sp, #16]",
    "mov x29, sp",
    "mov x0, x3",
    "mov x1, x4",
    "blr x16",
    "ldr x9, [sp, #16]",
    "ldr x10, [x9]",
    "ldp x29, x30, [sp]",
    "mov sp, x10",
    "ret",
    ".globl _trust_cg_owned_stack_context_output_end",
    ".private_extern _trust_cg_owned_stack_context_output_end",
    "_trust_cg_owned_stack_context_output_end:",
);

unsafe extern "C" {
    fn trust_cg_owned_stack_context_output(
        target: *const u8,
        host: *mut HostContext,
        sp: usize,
        context: *const u8,
        output: *mut u8,
    );
    fn trust_cg_owned_stack_context_output_end();
}

pub(super) fn check_actual() -> Result<(), EntryStackError> {
    let begin = trust_cg_owned_stack_context_output as *const () as usize;
    let end = trust_cg_owned_stack_context_output_end as *const () as usize;
    let len = end.checked_sub(begin).ok_or(EntryStackError::Adapter)?;
    if len != 15 * 4 || !begin.is_multiple_of(4) {
        return Err(EntryStackError::Adapter);
    }
    // SAFETY: private symbols delimit precisely this immutable 60-byte routine.
    let bytes = unsafe { std::slice::from_raw_parts(begin as *const u8, len) };
    check_words(bytes)
}

fn check_words(bytes: &[u8]) -> Result<(), EntryStackError> {
    // Independent A64 encoding contract. Save the genuine host SP and header
    // FIRST, then place the actual pointer arguments in X0/X1. BLR's PC+4 LR
    // is returned to this continuation; host SP/FP/LR are restored afterward.
    // No X0 scalar result is read or reinterpreted on this void path.
    let expected = [
        0x9100_03e9_u32,
        0xf900_0029,
        0xaa00_03f0,
        0x9100_005f,
        0xa900_7bfd,
        0xf900_0be1,
        0x9100_03fd,
        0xaa03_03e0,
        0xaa04_03e1,
        0xd63f_0200,
        0xf940_0be9,
        0xf940_012a,
        0xa940_7bfd,
        0x9100_015f,
        0xd65f_03c0,
    ];
    if bytes.len() != expected.len() * 4
        || bytes
            .as_chunks::<4>()
            .0
            .iter()
            .zip(expected)
            .any(|(actual, expected)| *actual != expected.to_le_bytes())
    {
        return Err(EntryStackError::Adapter);
    }
    Ok(())
}

/// Requires the original source/byte, ABI and exclusive storage consumer to
/// retain every target/context/output/stack allocation and execution lease.
/// Ordinary signals must already be blocked by the original stack owner.
pub(super) unsafe fn invoke(
    target: *const u8,
    host: &mut HostContext,
    sp: usize,
    context: *const u8,
    output: *mut u8,
) {
    // SAFETY: only the sealed consumer can call this private adapter with its
    // exact two-pointer/void source and complete checked memory/return contract.
    unsafe { trust_cg_owned_stack_context_output(target, host, sp, context, output) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn actual_void_adapter_and_each_instruction_binding_are_checked() {
        check_actual().unwrap();
        let begin = trust_cg_owned_stack_context_output as *const () as usize;
        // SAFETY: check_actual just established this exact immutable extent.
        let original = unsafe { std::slice::from_raw_parts(begin as *const u8, 60) };
        for word in 0..15 {
            let mut changed = original.to_vec();
            changed[word * 4] ^= 1;
            assert!(check_words(&changed).is_err(), "changed word {word}");
        }
        assert!(check_words(&original[..56]).is_err());
    }
}
