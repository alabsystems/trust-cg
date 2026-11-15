#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
static I64S: [i64; 3] = [10, 20, 30];
#[inline(never)]
fn sf(xs: &[i64]) -> i64 {
    match xs.split_first() {
        Some((h, _)) => *h,
        None => -99,
    }
}
#[no_mangle]
pub extern "C" fn a(k: u32) -> i64 {
    sf(&I64S[(k % 4) as usize..])
}
