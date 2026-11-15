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
pub extern "C" fn condswap(x: f64, y: f64) -> f64 {
    let (mut a, mut b) = (x, y);
    let mut i = 0;
    while i < 5 {
        if a > b {
            let t = a;
            a = b;
            b = t;
        } else {
            a = a + 1.0;
        }
        i += 1;
    }
    a * 100.0 + b
}
