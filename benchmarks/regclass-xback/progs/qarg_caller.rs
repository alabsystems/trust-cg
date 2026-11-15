// CALLER: exits 42 only when both 128-bit lanes and the tag survive the call.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
extern crate regclassqarg;
fn main() {
    let v: u128 = (7u128 << 64) | 13u128;
    std::process::exit(regclassqarg::take(Some(v)) + regclassqarg::take(None));
}
