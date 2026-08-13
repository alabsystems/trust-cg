// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression coverage for AArch64's non-trapping integer division semantics.

mod common;

use common::a64_interp::A64Interp;

const SDIV_W0_W0_W1: u32 = 0x1ac1_0c00;
const SDIV_X0_X0_X1: u32 = 0x9ac1_0c00;
const UDIV_X0_X0_X1: u32 = 0x9ac1_0800;
const RET: u32 = 0xd65f_03c0;

fn run(instruction: u32, lhs: u64, rhs: u64) -> u64 {
    let text = [instruction, RET]
        .into_iter()
        .flat_map(u32::to_le_bytes)
        .collect();
    let mut interp = A64Interp::new(text);
    interp.set_x(0, lhs);
    interp.set_x(1, rhs);
    interp.run(0).expect("division snippet must execute")
}

#[test]
fn signed_division_overflow_returns_the_dividend_without_trapping() {
    assert_eq!(
        run(SDIV_X0_X0_X1, i64::MIN as u64, (-1_i64) as u64),
        i64::MIN as u64
    );
    assert_eq!(
        run(
            SDIV_W0_W0_W1,
            i32::MIN as u32 as u64,
            (-1_i32) as u32 as u64
        ),
        i32::MIN as u32 as u64
    );
}

#[test]
fn integer_division_by_zero_returns_zero() {
    assert_eq!(run(SDIV_X0_X0_X1, u64::MAX, 0), 0);
    assert_eq!(run(UDIV_X0_X0_X1, u64::MAX, 0), 0);
}
