#![no_std]
#![allow(dead_code)]
#![feature(core_float_math, float_minimum_maximum, core_intrinsics)]
#![allow(internal_features)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
use core::intrinsics as I;
#[no_mangle]
pub extern "C" fn log2_32(a: f32) -> f32 {
    I::log2f32(a)
}
