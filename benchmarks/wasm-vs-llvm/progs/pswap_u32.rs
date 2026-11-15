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
pub extern "C" fn pswap_u32(i: u32, j: u32) -> u32 {
    let mut a = [1u32, 2, 3, 4, 5, 6, 7];
    swap_idx(&mut a, (i % 7) as usize, (j % 7) as usize);
    swap_idx(&mut a, (j % 5) as usize, 6);
    a.iter().fold(0, |h, &x| h * 10 + x)
}
