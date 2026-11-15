// CALLEE: a 128-bit-lane scalar pair in the ARGUMENT direction. `Option<u128>`
// is 32 bytes and rustc still classifies it `PassMode::Pair` — of two `i128`
// scalars, each of which AAPCS64 §5.4 splits across TWO registers, so the whole
// value rides x0-x3. trust-cg's whole-slot classification sends anything over 16
// bytes through a caller-allocated copy addressed by pointer, which is a
// DIFFERENT convention entirely.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![crate_type = "rlib"]
#![crate_name = "regclassqarg"]
#[inline(never)]
pub fn take(o: Option<u128>) -> i32 {
    match o {
        // Reads the HIGH half of the payload as well as the low one, so a lane
        // pair placed at the wrong register or the wrong offset is visible.
        Some(v) => ((v >> 64) as i32) + (v as i32),
        None => 22,
    }
}
