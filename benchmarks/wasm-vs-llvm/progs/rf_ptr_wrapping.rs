#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
static U16S: [u16; 4] = [1, 2, 3, 4];
#[no_mangle]
pub extern "C" fn pw(a: u32) -> u32 {
    let p = U16S.as_ptr();
    (p.wrapping_add(a as usize).wrapping_sub(a as usize) == p) as u32
}
