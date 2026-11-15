#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
#[no_mangle]
pub extern "C" fn ri(a: u32) -> u32 {
    let lo = (a as u8).saturating_sub(3);
    let mut acc = 0u32;
    for i in lo..=(a as u8) {
        acc = acc * 3 + i as u32;
    }
    acc
}
