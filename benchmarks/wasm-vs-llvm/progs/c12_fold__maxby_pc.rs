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
pub extern "C" fn maxby_pc(a: f32, b: f32) -> f32 {
    let v = [a, b, a + b, 1.0];
    let mut m = v[0];
    for &x in &v[1..] {
        if x.partial_cmp(&m) == Some(core::cmp::Ordering::Greater) {
            m = x
        }
    }
    m
}
