#![no_std]
#[unsafe(no_mangle)] pub unsafe extern "C" fn cast_int_to_ref(p:usize)->&'static u64 { unsafe { core::mem::transmute::<usize, &'static u64>(p) } }
