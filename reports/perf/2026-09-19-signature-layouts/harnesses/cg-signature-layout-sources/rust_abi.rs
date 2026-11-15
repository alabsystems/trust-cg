#![no_std]
#[repr(C)]
pub struct Ordered { pub small: u8, pub wide: u64 }
pub struct Reordered { pub small: u8, pub wide: u64 }
#[repr(C, packed)]
pub struct Packed { pub small: u8, pub wide: u64 }
#[repr(C)]
pub struct Nested { pub values: [u64; 2], pub last: u64 }
#[unsafe(no_mangle)]
pub fn layout_rust_abi(_value: &Ordered) -> u64 { 7 }
