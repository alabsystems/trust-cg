#![no_std]
#[unsafe(no_mangle)] pub extern "C" fn cast_refmut_scalar(p:&mut u64)->usize { p as *mut u64 as usize }
