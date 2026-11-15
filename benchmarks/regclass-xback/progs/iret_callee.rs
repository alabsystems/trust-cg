// CALLEE: the integer scalar pair in the RETURN direction.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// `Q` is a `#[repr(Rust)]` two-`i32` struct: `BackendRepr::ScalarPair`, which
// rustc classifies `PassMode::Pair` — TWO ABI values, so LLVM returns it in
// `w0` AND `w1` (`ldr w0 ; ldur w1 ; ret`). The bridge's uniform lane slot is
// ONE 8-byte composite, and the C rule trust-cg's classifier applies to a
// composite of 8 bytes or fewer puts it WHOLE into ONE register (`ldr x0,[x1]`)
// — the same bytes, one register too few.
#![crate_type = "rlib"]
#![crate_name = "regclassiret"]
pub struct Q {
    pub a: i32,
    pub b: i32,
}
#[inline(never)]
pub fn make(x: i32) -> Q {
    Q { a: x, b: x + 2 }
}
