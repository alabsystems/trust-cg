#![no_std]
#[unsafe(no_mangle)] pub extern "C" fn cast_ref_scalar(p:&u64)->usize { p as *const u64 as usize }
