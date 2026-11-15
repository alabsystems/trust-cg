// CALLEE: a TAGGED ENUM by-value argument whose `PassMode::Pair` lanes are the
// tag and the payload (`Option<u32>`: `4 bytes @0 ; 4 bytes @4`) — the 25-root
// family of the `core` census, and the one that also exercises the bridge's
// memory-enum tag slot rather than a plain struct.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![crate_type = "rlib"]
#![crate_name = "regclassearg"]
#[inline(never)]
pub fn take(o: Option<u32>) -> i32 {
    match o {
        Some(v) => v as i32,
        None => 22,
    }
}
