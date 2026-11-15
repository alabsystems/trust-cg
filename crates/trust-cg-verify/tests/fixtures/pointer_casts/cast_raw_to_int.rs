#![no_std]
#[unsafe(no_mangle)] pub extern "C" fn cast_raw_to_int(p:*mut u8)->isize { p as isize }
