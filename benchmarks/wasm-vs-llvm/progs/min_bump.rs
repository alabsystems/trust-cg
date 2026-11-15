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
fn advance(s: &mut &[u8]) {
    *s = &s[1..];
}
#[no_mangle]
pub extern "C" fn adv(k: u32) -> u32 {
    let a = [1u8, 2, 3, 4, 5];
    let mut s: &[u8] = &a[(k % 3) as usize..];
    advance(&mut s);
    s.len() as u32 * 100 + s[0] as u32
}
