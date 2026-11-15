// CALLEE: a 4-byte integer scalar pair in the ARGUMENT direction — rustc puts
// the two 16-bit scalars in two argument registers (lanes `2 bytes @0 ;
// 2 bytes @2`), the 14-root family of the `core` census (`flt2dec`'s
// `(i16, i16)`).
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![crate_type = "rlib"]
#![crate_name = "regclassharg"]
#[inline(never)]
pub fn take(q: (i16, i16)) -> i32 {
    // Asymmetric in the two lanes, so a swapped or duplicated lane is visible.
    q.0 as i32 * 2 + q.1 as i32
}
