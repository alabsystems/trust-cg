#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
static A: [u8; 5] = [1, 2, 3, 4, 5];
static B: [u8; 3] = [10, 20, 30];
static TAB: [&[u8]; 2] = [&A, &B];
#[no_mangle]
pub extern "C" fn g(k: u32) -> u32 {
    let mut acc = k;
    for s in TAB.iter() {
        acc = acc.wrapping_add(s.len() as u32);
    }
    acc
}
