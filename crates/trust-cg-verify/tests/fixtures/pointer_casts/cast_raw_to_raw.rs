#![no_std]
#[unsafe(no_mangle)] pub extern "C" fn cast_raw_to_raw(p:*const u64)->*mut u8 { p as *mut u8 }
