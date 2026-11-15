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
pub extern "C" fn z(k: u32) -> u32 {
    let a = [1u16, 2, 3, 4];
    let b = [10u64, 20, 30, 40];
    let mut acc = 0u32;
    for (x, y) in a[..(k % 5) as usize].iter().zip(b.iter()) {
        acc = acc * 100 + *x as u32 + *y as u32;
    }
    acc
}
