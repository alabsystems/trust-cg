#![no_std]
#![allow(dead_code)]

use core::cmp::Ordering;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[no_mangle]
pub extern "C" fn found_loop(a: u32) -> u32 {
    let mut found = None;
    for i in 0..16u32 {
        if (a >> (i * 2)) & 3 == 3 {
            found = Some(i);
        }
    }
    match found {
        Some(i) => i,
        None => 99,
    }
}
