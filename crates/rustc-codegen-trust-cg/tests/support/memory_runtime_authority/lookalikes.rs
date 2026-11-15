// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// Deliberately inert bodies: this input is only analyzed, never code-generated.
#![no_std]

include!("declarations.rs");

#[no_mangle]
pub unsafe extern "C" fn memcpy(dst: *mut c_void, _src: *const c_void, _n: usize) -> *mut c_void {
    dst
}

#[no_mangle]
pub unsafe extern "C" fn memmove(dst: *mut c_void, _src: *const c_void, _n: usize) -> *mut c_void {
    dst
}

#[no_mangle]
pub unsafe extern "C" fn memset(dst: *mut c_void, _value: c_int, _n: usize) -> *mut c_void {
    dst
}
