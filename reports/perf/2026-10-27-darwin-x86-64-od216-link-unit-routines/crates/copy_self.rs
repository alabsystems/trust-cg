// Ruling OD-216, the circular case: the crate's own `memmove` copies through
// `ptr::copy`, which lowers to an LIR `Memmove`, the selector's `call
// memmove`: it calls itself.
#![no_std]

use core::ffi::c_void;

/// The crate's own `memmove`, through itself.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memmove(dest: *mut c_void, src: *const c_void, n: usize) -> *mut c_void {
    unsafe { core::ptr::copy(src as *const u8, dest as *mut u8, n) };
    dest
}
