// CALLEE: the float scalar pair in the RETURN direction.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// `P` is a `#[repr(Rust)]` two-`f64` struct: `BackendRepr::ScalarPair`, which
// rustc classifies `PassMode::Pair`. AAPCS64 §6.4.2 gives each member of a
// homogeneous floating aggregate its own SIMD&FP register, so LLVM returns it
// in `d0`/`d1` (`fmul d0 ; fmul d1 ; ret`). The bridge's uniform INTEGER lane
// slot would return it in the GPR pair — the same bytes, the wrong register
// file, and a self-consistent backend never notices.
//
// `#[inline(never)]` plus a separate crate is what makes the call cross a
// codegen boundary: without both, the caller inlines the callee and the two
// halves can never disagree.
#![crate_type = "rlib"]
#![crate_name = "regclassfret"]
pub struct P {
    pub a: f64,
    pub b: f64,
}
#[inline(never)]
pub fn make(x: f64) -> P {
    P { a: x * 2.0, b: x * 20.0 }
}
