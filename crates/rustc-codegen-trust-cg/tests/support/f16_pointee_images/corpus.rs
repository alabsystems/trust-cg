#![no_std]
#![feature(f16)]
use core::arch::aarch64::{float16x4_t, float16x8_t};
#[inline(never)]
fn as_array4(v: &float16x4_t) -> &[f16; 4] {
    unsafe { &*(v as *const float16x4_t as *const [f16; 4]) }
}
#[inline(never)]
fn as_array8(v: &float16x8_t) -> &[f16; 8] {
    unsafe { &*(v as *const float16x8_t as *const [f16; 8]) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn array4(p: *const float16x4_t) -> *const u16 {
    as_array4(unsafe { &*p }).as_ptr().cast()
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn array8(p: *const float16x8_t) -> *const u16 {
    as_array8(unsafe { &*p }).as_ptr().cast()
}

#[inline(never)]
fn as_mut_array4(v: &mut float16x4_t) -> &mut [f16; 4] {
    unsafe { &mut *(v as *mut float16x4_t as *mut [f16; 4]) }
}
#[inline(never)]
fn as_mut_array8(v: &mut float16x8_t) -> &mut [f16; 8] {
    unsafe { &mut *(v as *mut float16x8_t as *mut [f16; 8]) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn array_mut4(p: *mut float16x4_t) -> *mut u16 {
    as_mut_array4(unsafe { &mut *p }).as_mut_ptr().cast()
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn array_mut8(p: *mut float16x8_t) -> *mut u16 {
    as_mut_array8(unsafe { &mut *p }).as_mut_ptr().cast()
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn offset16(p: *mut f16, index: usize) -> *mut u16 {
    unsafe { p.add(index) }.cast()
}
