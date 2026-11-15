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
pub extern "C" fn result_loop(a: u32) -> i32 {
    let mut r: Result<u32, u8> = Ok(0);
    for i in 0..8u32 {
        r = match r {
            Ok(v) if (a >> i) & 1 == 1 => Ok(v + i),
            Ok(v) if v > 10 => Err(i as u8),
            other => other,
        };
    }
    match r {
        Ok(v) => v as i32,
        Err(e) => -(e as i32),
    }
}
