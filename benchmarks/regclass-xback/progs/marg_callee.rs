// CALLEE: a MIXED-WIDTH integer scalar pair in the ARGUMENT direction — rustc's
// lanes are `4 bytes @0 ; 2 bytes @4`, the 6-root family of the `core` census
// (`fmt::PostPadding`). The second lane is NARROWER than the first, so a plan
// that synthesised lane offsets from the carriers' widths instead of reading
// rustc's own would place it wrong.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![crate_type = "rlib"]
#![crate_name = "regclassmarg"]
pub struct M {
    pub a: u32,
    pub b: u16,
}
#[inline(never)]
pub fn take(m: M) -> i32 {
    m.a as i32 * 2 + m.b as i32
}
