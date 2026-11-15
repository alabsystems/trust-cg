#![no_std]
pub struct Reordered { pub a:u8, pub b:u64 }
#[unsafe(no_mangle)] pub extern "C" fn cast_ref_reordered(p:&Reordered)->usize { p as *const Reordered as usize }
