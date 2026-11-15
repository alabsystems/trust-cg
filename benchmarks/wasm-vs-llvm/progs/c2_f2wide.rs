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
#[no_mangle]
pub extern "C" fn f64_i32(x: f64) -> i32 {
    x as i32
}
#[no_mangle]
pub extern "C" fn f64_u32(x: f64) -> u32 {
    x as u32
}
#[no_mangle]
pub extern "C" fn f32_i64(x: f32) -> i64 {
    x as i64
}
#[no_mangle]
pub extern "C" fn f32_u64(x: f32) -> u64 {
    x as u64
}
#[no_mangle]
pub extern "C" fn f64_i64(x: f64) -> i64 {
    x as i64
}
#[no_mangle]
pub extern "C" fn f64_u64(x: f64) -> u64 {
    x as u64
}
#[no_mangle]
pub extern "C" fn f64_usize(x: f64) -> u64 {
    (x as usize) as u64
}
#[no_mangle]
pub extern "C" fn f64_isize(x: f64) -> i64 {
    (x as isize) as i64
}
#[no_mangle]
pub extern "C" fn f32_usize(x: f32) -> u32 {
    (x as usize) as u32
}
#[no_mangle]
pub extern "C" fn f32_isize(x: f32) -> i32 {
    (x as isize) as i32
}
