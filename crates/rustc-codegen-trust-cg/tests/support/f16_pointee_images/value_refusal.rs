#![no_std]
#![feature(f16)]
#[unsafe(no_mangle)]
pub fn f16_value_add(a: f16, b: f16) -> f16 {
    a + b
}
#[unsafe(no_mangle)]
pub unsafe fn f16_value_load(p: *const f16) -> f16 {
    unsafe { *p }
}
