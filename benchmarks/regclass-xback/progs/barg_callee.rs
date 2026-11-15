// CALLEE: a SUB-EIGHTBYTE integer scalar pair in the ARGUMENT direction, with a
// `zeroext` tag lane. `Option<u8>` is 2 bytes and rustc's `PassMode::Pair` puts
// its tag in the first argument register (ArgAttributes `arg_ext: Zext`) and its
// payload in the second; trust-cg's whole-slot classification put the whole
// 2-byte composite in ONE register, which is the `1 byte @0 ; 1 byte @1` family
// of the `core` census (27 roots on AArch64, the same shape on x86-64).
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![crate_type = "rlib"]
#![crate_name = "regclassbarg"]
#[inline(never)]
pub fn take(o: Option<u8>) -> i32 {
    match o {
        Some(v) => v as i32,
        None => 22,
    }
}
