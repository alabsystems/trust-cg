#![no_std]
#[unsafe(no_mangle)] pub extern "C" fn cast_int_to_const(p:usize)->*const u64 { p as *const u64 }
