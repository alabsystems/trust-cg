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
pub extern "C" fn sw(a: u32, b: u32) -> u64 {
    let mut buf = [1u64, 2, 3, 4, 5, 6];
    buf.swap((a % 6) as usize, (b % 6) as usize);
    buf[0] ^ buf[1] << 8 ^ buf[5] << 16
}
