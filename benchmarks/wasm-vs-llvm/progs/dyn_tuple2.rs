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
struct Ci {
    r: f64,
    n: u8,
}
#[inline(never)]
fn area(c: &Ci) -> f64 {
    c.r + c.n as f64
}
#[no_mangle]
pub extern "C" fn ref_ci(b: f64) -> f64 {
    let c = Ci { r: b, n: 3 };
    area(&c)
}
