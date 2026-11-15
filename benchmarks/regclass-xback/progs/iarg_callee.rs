// CALLEE: the integer scalar pair in the ARGUMENT direction (rustc's
// `PassMode::Pair` puts the two 32-bit scalars in `w0` AND `w1`).
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![crate_type = "rlib"]
#![crate_name = "regclassiarg"]
pub struct Q {
    pub a: i32,
    pub b: i32,
}
#[inline(never)]
pub fn take(q: Q) -> i32 {
    q.a + q.b
}
