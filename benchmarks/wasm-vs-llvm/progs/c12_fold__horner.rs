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
fn arr(a: f64, b: f64) -> [f64; 6] {
    [a, b, a * b, a - b, a / (b + 1.0), 0.25]
}
#[no_mangle]
pub extern "C" fn horner(x: f64) -> f64 {
    let c = [1.0, -0.5, 0.25, -0.125, 1e-3, 7.0];
    c.iter().rev().fold(0.0, |acc, &k| acc * x + k)
}
