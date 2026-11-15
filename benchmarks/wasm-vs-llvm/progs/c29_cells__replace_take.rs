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
use core::cell::Cell;
use core::sync::atomic::{AtomicU32, AtomicU64, Ordering};
static AF: AtomicU32 = AtomicU32::new(0x3f80_0000);
static AD: AtomicU64 = AtomicU64::new(0);
#[no_mangle]
pub extern "C" fn replace_take(a: f32, b: f32) -> f32 {
    let mut x = a;
    let old = core::mem::replace(&mut x, b);
    let t = core::mem::take(&mut x);
    old * 10.0 + t + x
}
