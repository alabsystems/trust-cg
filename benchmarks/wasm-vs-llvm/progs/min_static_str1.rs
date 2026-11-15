#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
static TEXT: &str = "hello";
#[no_mangle]
pub extern "C" fn tl() -> u32 {
    TEXT.len() as u32
}
