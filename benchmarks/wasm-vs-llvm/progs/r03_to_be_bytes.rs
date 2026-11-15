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
pub extern "C" fn f(a: u32) -> u32 {
    let b = a.to_be_bytes();
    b[0] as u32 ^ (b[3] as u32) << 8
}
