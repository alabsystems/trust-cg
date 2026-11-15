#![no_std]
#![feature(core_float_math, float_minimum_maximum)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
#[no_mangle]
pub extern "C" fn fl(a: f64) -> f64 {
    core::f64::math::floor(a)
}
#[no_mangle]
#[no_mangle]
pub extern "C" fn fm(a: f64, b: f64) -> f64 {
    core::f64::math::mul_add(a, b, 0.1)
}
#[no_mangle]
pub extern "C" fn mn(a: f64, b: f64) -> f64 {
    a.minimum(b)
}
