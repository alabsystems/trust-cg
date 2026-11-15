#![no_std]
#![allow(dead_code)]
#![feature(core_float_math, float_minimum_maximum)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
use core::f32::math as m32;
use core::f64::math as m64;
#[no_mangle]
pub extern "C" fn sqrt64(a: f64) -> f64 {
    m64::sqrt(a)
}
#[no_mangle]
pub extern "C" fn sqrt32(a: f32) -> f32 {
    m32::sqrt(a)
}
#[no_mangle]
pub extern "C" fn fma64(a: f64, b: f64, c: f64) -> f64 {
    m64::mul_add(a, b, c)
}
#[no_mangle]
pub extern "C" fn fma32(a: f32, b: f32, c: f32) -> f32 {
    m32::mul_add(a, b, c)
}
#[no_mangle]
pub extern "C" fn powi64(a: f64, n: i32) -> f64 {
    m64::powi(a, n)
}
#[no_mangle]
pub extern "C" fn powi32(a: f32, n: i32) -> f32 {
    m32::powi(a, n)
}
#[no_mangle]
pub extern "C" fn diveu64(a: f64, b: f64) -> f64 {
    m64::div_euclid(a, b)
}
#[no_mangle]
pub extern "C" fn remeu64(a: f64, b: f64) -> f64 {
    m64::rem_euclid(a, b)
}
#[no_mangle]
pub extern "C" fn remeu32(a: f32, b: f32) -> f32 {
    m32::rem_euclid(a, b)
}
#[no_mangle]
pub extern "C" fn fma_exact(a: f64) -> f64 {
    let b = a * (1.0 + f64::EPSILON);
    m64::mul_add(a, b, -(a * b))
}
