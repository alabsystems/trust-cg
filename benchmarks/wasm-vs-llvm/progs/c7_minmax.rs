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
pub extern "C" fn min32(a: f32, b: f32) -> f32 {
    a.min(b)
}
#[no_mangle]
pub extern "C" fn max64(a: f64, b: f64) -> f64 {
    a.max(b)
}
#[no_mangle]
pub extern "C" fn clamp64(a: f64, b: f64) -> f64 {
    if b.is_nan() || b < 0.0 {
        return -3.0;
    }
    a.clamp(-b, b)
}
#[no_mangle]
pub extern "C" fn clamp32(a: f32) -> f32 {
    a.clamp(-1.5, 2.25)
}
#[no_mangle]
pub extern "C" fn minimum64(a: f64, b: f64) -> f64 {
    a.minimum(b)
}
#[no_mangle]
pub extern "C" fn maximum32(a: f32, b: f32) -> f32 {
    a.maximum(b)
}
#[no_mangle]
pub extern "C" fn copysign64(a: f64, b: f64) -> f64 {
    a.copysign(b)
}
#[no_mangle]
pub extern "C" fn copysign32(a: f32, b: f32) -> u32 {
    a.copysign(b).to_bits() & 0x807f_ffff | ((a.is_nan() as u32) << 23)
}
#[no_mangle]
pub extern "C" fn abs_signum(a: f64) -> f64 {
    a.abs() * 3.0 + a.signum()
}
#[no_mangle]
pub extern "C" fn abs32bits(a: f32) -> u32 {
    a.abs().to_bits()
}
