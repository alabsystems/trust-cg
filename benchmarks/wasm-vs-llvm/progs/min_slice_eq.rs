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
fn eq8(a: &[u8], b: &[u8]) -> bool {
    a == b
}
#[no_mangle]
pub extern "C" fn e(k: u32) -> u32 {
    let x = [1u8, 2, 3];
    let y = [1u8, 2, (k % 4) as u8];
    eq8(&x, &y) as u32
}
