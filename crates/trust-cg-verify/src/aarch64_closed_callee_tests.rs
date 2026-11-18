// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const CALLER: u64 = 0x100;
const CALLEE: u64 = 0x200;
const PRINT: u64 = 0x300;
const EXIT: u64 = 0x400;
const ADD: u32 = 0x9100_0421;
const RET: u32 = 0xd65f_03c0;
const BRK: u32 = 0xd420_0020;

fn bytes(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|word| word.to_le_bytes()).collect()
}

fn bl(pc: u64, target: u64) -> u32 {
    let displacement = (target as i64 - pc as i64) / 4;
    0x9400_0000 | (displacement as u32 & 0x03ff_ffff)
}

fn check(
    caller_start: u32,
    instructions: &[u32],
    print: &str,
) -> Result<(), ClosedAarch64CallError> {
    check_linked_control(
        &Aarch64ClosedCallText {
            caller: &bytes(&[caller_start, bl(CALLER + 4, CALLEE), BRK]),
            caller_address: CALLER,
            callee: &bytes(instructions),
            callee_address: CALLEE,
            call_offset: 4,
            callee_calls: &[
                ResolvedClosedCalleeCall {
                    offset: 0,
                    symbol: print,
                    target: PRINT,
                },
                ResolvedClosedCalleeCall {
                    offset: 8,
                    symbol: "exit",
                    target: EXIT,
                },
            ],
        },
        &["print", "exit"],
    )
}

fn callee() -> [u32; 4] {
    [bl(CALLEE, PRINT), ADD, bl(CALLEE + 8, EXIT), BRK]
}

#[test]
fn two_potentially_returning_calls_cannot_return_from_the_trapping_callee() {
    assert!(check(ADD, &callee(), "print").is_ok());
}

#[test]
fn rejects_a_direct_branch_into_the_call_continuation() {
    for branch in [0x1400_0002, 0x5400_0042, 0xb400_0040] {
        assert!(matches!(
            check(branch, &callee(), "print"),
            Err(ClosedAarch64CallError::CallerControl(0))
        ));
    }
}

#[test]
fn refuses_return_tail_transfer_and_nonterminal_trap() {
    for changed in [RET, 0x1400_0001, 0xd63f_0000, BRK] {
        let mut instructions = callee();
        instructions[1] = changed;
        assert!(matches!(
            check(ADD, &instructions, "print"),
            Err(ClosedAarch64CallError::CalleeControl(4))
        ));
    }
    let mut instructions = callee();
    instructions[3] = ADD;
    assert!(matches!(
        check(ADD, &instructions, "print"),
        Err(ClosedAarch64CallError::CalleeControl(12))
    ));
}

#[test]
fn refuses_a_wrong_import_or_a_direct_call_back_into_either_body() {
    assert!(matches!(
        check(ADD, &callee(), "replacement"),
        Err(ClosedAarch64CallError::CalleeCalls)
    ));
    for target in [CALLEE + 4, CALLER + 4] {
        let mut instructions = callee();
        instructions[0] = bl(CALLEE, target);
        assert!(matches!(
            check(ADD, &instructions, "print"),
            Err(ClosedAarch64CallError::CalleeCalls)
        ));
    }
}
