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
pub extern "C" fn i32_f32(x: i32) -> f32 {
    x as f32
}
#[no_mangle]
pub extern "C" fn u32_f32(x: u32) -> f32 {
    x as f32
}
#[no_mangle]
pub extern "C" fn i64_f32(x: i64) -> f32 {
    x as f32
}
#[no_mangle]
pub extern "C" fn u64_f32(x: u64) -> f32 {
    x as f32
}
#[no_mangle]
pub extern "C" fn i64_f64(x: i64) -> f64 {
    x as f64
}
#[no_mangle]
pub extern "C" fn u64_f64(x: u64) -> f64 {
    x as f64
}
#[no_mangle]
pub extern "C" fn u32_f64(x: u32) -> f64 {
    x as f64
}
#[no_mangle]
pub extern "C" fn narrow_f32(x: i32) -> f32 {
    (x as i8) as f32 + (x as u8) as f32 * 3.0 + (x as i16) as f32 * 7.0 + (x as u16) as f32 * 11.0
}
#[no_mangle]
pub extern "C" fn usize_f32(x: u32) -> f32 {
    (x as usize) as f32 + ((x as isize) as f64 * 0.5) as f32
}
#[no_mangle]
pub extern "C" fn narrow_f64(x: i32) -> f64 {
    (x as i8) as f64 + (x as u8) as f64 * 3.0 + (x as i16) as f64 * 7.0 + (x as u16) as f64 * 11.0
}
