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
pub extern "C" fn swp(a: i64, b: u32) -> i64 {
    let mut v = [a as i128, -(a as i128), (a as i128) << 70];
    v.swap((b % 3) as usize, ((b / 3) % 3) as usize);
    (v[0] ^ (v[1] >> 64) ^ (v[2] >> 7)) as i64
}
