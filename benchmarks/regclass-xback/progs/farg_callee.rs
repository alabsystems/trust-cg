// CALLEE: the float scalar pair in the ARGUMENT direction (AAPCS64 §6.4.2
// passes each member in its own SIMD&FP register, `d0`/`d1`).
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![crate_type = "rlib"]
#![crate_name = "regclassfarg"]
pub struct P {
    pub a: f64,
    pub b: f64,
}
#[inline(never)]
pub fn take(p: P) -> i32 {
    let mut code = 0;
    if p.a == 4.0 { code += 2; }
    if p.b == 40.0 { code += 40; }
    code
}
