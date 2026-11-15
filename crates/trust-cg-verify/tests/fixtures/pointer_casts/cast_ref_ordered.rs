#![no_std]
#[repr(C)] pub struct Ordered { pub a:u8, pub b:u64 }
#[unsafe(no_mangle)] pub extern "C" fn cast_ref_ordered(p:&Ordered)->usize { p as *const Ordered as usize }
