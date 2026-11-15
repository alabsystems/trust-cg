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
pub extern "C" fn cell(a: f64, b: f64) -> f64 {
    let c = Cell::new(a);
    let old = c.replace(b);
    c.set(c.get() * 2.0 + old);
    c.get()
}
