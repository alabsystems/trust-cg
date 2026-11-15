#![no_std]
#[unsafe(no_mangle)] pub extern "C" fn cast_int_to_mut(p:isize)->*mut u8 { p as *mut u8 }
