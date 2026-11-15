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
fn swap_idx<T: Copy>(a: &mut [T], i: usize, j: usize) {
    let p = a.as_mut_ptr();
    unsafe { core::ptr::swap(p.add(i), p.add(j)) }
}

#[no_mangle]
pub extern "C" fn pswap_i64(i: u32, j: u32) -> i64 {
    let mut a = [-1i64, 2, i64::MIN, 4, 1 << 40];
    swap_idx(&mut a, (i % 5) as usize, (j % 5) as usize);
    swap_idx(&mut a, 0, (i % 5) as usize);
    a.iter().fold(0i64, |h, &x| h.wrapping_mul(31) ^ x)
}
