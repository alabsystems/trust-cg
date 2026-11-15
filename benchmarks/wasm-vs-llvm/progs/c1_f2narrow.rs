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
pub extern "C" fn f32_i8(x: f32) -> i32 {
    (x as i8) as i32
}
#[no_mangle]
pub extern "C" fn f32_u8(x: f32) -> i32 {
    (x as u8) as i32
}
#[no_mangle]
pub extern "C" fn f32_i16(x: f32) -> i32 {
    (x as i16) as i32
}
#[no_mangle]
pub extern "C" fn f32_u16(x: f32) -> i32 {
    (x as u16) as i32
}
#[no_mangle]
pub extern "C" fn f32_i32(x: f32) -> i32 {
    x as i32
}
#[no_mangle]
pub extern "C" fn f32_u32(x: f32) -> u32 {
    x as u32
}
#[no_mangle]
pub extern "C" fn f64_i8(x: f64) -> i32 {
    (x as i8) as i32
}
#[no_mangle]
pub extern "C" fn f64_u8(x: f64) -> i32 {
    (x as u8) as i32
}
#[no_mangle]
pub extern "C" fn f64_i16(x: f64) -> i32 {
    (x as i16) as i32
}
#[no_mangle]
pub extern "C" fn f64_u16(x: f64) -> i32 {
    (x as u16) as i32
}
