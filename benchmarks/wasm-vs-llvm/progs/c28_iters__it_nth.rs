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
#[inline(never)]
fn mk(a: f64, b: f64) -> [f64; 7] {
    [a, b, a + b, a * 0.5, -b, 1.25, a - 3.0]
}
#[inline(never)]
fn mk32(a: f32, b: f32) -> [f32; 7] {
    [a, b, a + b, a * 0.5, -b, 1.25, a - 3.0]
}
#[no_mangle]
pub extern "C" fn it_nth(a: f32, b: f32, k: i32) -> f32 {
    let v = mk32(a, b);
    *v.iter().nth((k & 7) as usize).unwrap_or(&-1.0)
}
