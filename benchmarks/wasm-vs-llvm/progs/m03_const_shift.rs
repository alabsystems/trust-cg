#![allow(arithmetic_overflow)]
#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[inline(never)]
fn sh9(x: u8) -> u8 {
    x << 9
}
#[inline(never)]
fn shr17(x: i16) -> i16 {
    x >> 17
}
#[inline(never)]
fn sh40(x: u32) -> u32 {
    x << 40
}
#[inline(never)]
fn sh70(x: i64) -> i64 {
    x >> 70
}
#[no_mangle]
pub extern "C" fn cshift(a: u32) -> u64 {
    sh9(a as u8) as u64
        | (shr17(a as i16) as u16 as u64) << 8
        | (sh40(a) as u64) << 24 ^ sh70(a as i64 * -12345) as u64
}
