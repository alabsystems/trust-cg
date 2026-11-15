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
    r: u64,
    n: u8,
}
#[inline(never)]
fn area(c: &Ci) -> f64 {
    c.r as f64 + c.n as f64
}
#[no_mangle]
pub extern "C" fn ref_ci(x: f64) -> f64 {
    let c = Ci {
        r: x as u64,
        n: 3 as u8,
    };
    area(&c)
}
