// Copyright 2026 Andrew Yates | Apache-2.0
//! Fixed four-pointer/U64 host-stack adapter. Its target is supplied only by
//! the sealed installed Core entry consumer; this module grants no callability.

use super::{EntryStackError, HostContext};

std::arch::global_asm!(
    ".text",
    ".p2align 2",
    ".globl _trust_cg_owned_stack_four_pointer_status",
    ".private_extern _trust_cg_owned_stack_four_pointer_status",
    "_trust_cg_owned_stack_four_pointer_status:",
    "mov x9, sp",
    "str x9, [x1]",
    "mov x16, x0",
    "mov sp, x2",
    "stp x29, x30, [sp]",
    "str x1, [sp, #16]",
    "mov x29, sp",
    "mov x0, x3",
    "mov x1, x4",
    "mov x2, x5",
    "mov x3, x6",
    "blr x16",
    "ldr x9, [sp, #16]",
    "ldr x10, [x9]",
    "ldp x29, x30, [sp]",
    "mov sp, x10",
    "ret",
    ".globl _trust_cg_owned_stack_four_pointer_status_end",
    ".private_extern _trust_cg_owned_stack_four_pointer_status_end",
    "_trust_cg_owned_stack_four_pointer_status_end:",
);

unsafe extern "C" {
    fn trust_cg_owned_stack_four_pointer_status(
        target: *const u8,
        host: *mut HostContext,
        sp: usize,
        input0: *const u8,
        input1: *const u8,
        output0: *mut u8,
        output1: *mut u8,
    ) -> u64;
    fn trust_cg_owned_stack_four_pointer_status_end();
}

pub(super) fn check_actual() -> Result<(), EntryStackError> {
    let begin = trust_cg_owned_stack_four_pointer_status as *const () as usize;
    let end = trust_cg_owned_stack_four_pointer_status_end as *const () as usize;
    let len = end.checked_sub(begin).ok_or(EntryStackError::Adapter)?;
    if len != 17 * 4 || !begin.is_multiple_of(4) {
        return Err(EntryStackError::Adapter);
    }
    // SAFETY: private symbols delimit precisely this immutable 68-byte routine.
    let bytes = unsafe { std::slice::from_raw_parts(begin as *const u8, len) };
    check_words(bytes)
}

fn check_words(bytes: &[u8]) -> Result<(), EntryStackError> {
    // Independent A64 encoding contract. Save the genuine host SP and header
    // FIRST, then place the actual pointer arguments in X0-X3. BLR's PC+4 LR
    // is returned to this continuation; host SP/FP/LR are restored afterward.
    // X0 retains the exact full U64 status across the restoring continuation.
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
        0xaa05_03e2,
        0xaa06_03e3,
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
    input0: *const u8,
    input1: *const u8,
    output0: *mut u8,
    output1: *mut u8,
) -> u64 {
    // SAFETY: only the sealed consumer can call this private adapter with its
    // exact four-pointer/U64 source and complete checked memory/return contract.
    unsafe {
        trust_cg_owned_stack_four_pointer_status(target, host, sp, input0, input1, output0, output1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn actual_status_adapter_and_each_instruction_binding_are_checked() {
        check_actual().unwrap();
        let begin = trust_cg_owned_stack_four_pointer_status as *const () as usize;
        // SAFETY: check_actual just established this exact immutable extent.
        let original = unsafe { std::slice::from_raw_parts(begin as *const u8, 68) };
        for word in 0..17 {
            let mut changed = original.to_vec();
            changed[word * 4] ^= 1;
            assert!(check_words(&changed).is_err(), "changed word {word}");
        }
        assert!(check_words(&original[..64]).is_err());
    }
}
