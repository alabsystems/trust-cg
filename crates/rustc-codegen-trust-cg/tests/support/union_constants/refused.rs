#![no_std]
use core::mem::MaybeUninit;
#[cfg(case = "boolean")]
#[unsafe(no_mangle)]
pub extern "C" fn refused(dst: &mut MaybeUninit<bool>) {
    *dst = const { unsafe { core::mem::transmute::<u8, MaybeUninit<bool>>(2) } };
}
#[cfg(case = "reference")]
#[unsafe(no_mangle)]
pub extern "C" fn refused(dst: &mut MaybeUninit<&'static u8>) {
    *dst = const { unsafe { core::mem::transmute::<usize, MaybeUninit<&'static u8>>(1) } };
}
#[repr(C)]
pub union Partial {
    pub word: u64,
    pub byte: u8,
}
#[cfg(case = "partial")]
#[unsafe(no_mangle)]
pub extern "C" fn refused(dst: &mut Partial) {
    *dst = const { Partial { byte: 0xa5 } };
}
