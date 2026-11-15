#![no_std]
#[unsafe(no_mangle)] pub extern "C" fn cast_fat_to_int(p:*const [u8])->usize { p as *const u8 as usize }
