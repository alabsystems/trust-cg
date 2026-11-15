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
fn addr_of(p: *const u32) -> u32 {
    p as usize as u32
}
#[no_mangle]
pub extern "C" fn dist(a: u32) -> u32 {
    let src = [a, a ^ 1];
    let dst = [0u32; 2];
    let d = addr_of(src.as_ptr()).abs_diff(addr_of(dst.as_ptr()));
    (d >= 8) as u32 | (src[0] ^ dst[1]) << 1
}
#[inline(never)]
fn nonover(src: *const (), dst: *const (), size: usize, count: usize) -> bool {
    let src_usize = src as usize;
    let dst_usize = dst as usize;
    let Some(size) = size.checked_mul(count) else {
        return false;
    };
    let diff = src_usize.abs_diff(dst_usize);
    diff >= size
}
#[no_mangle]
pub extern "C" fn nov(a: u32, b: u32) -> u32 {
    nonover(a as usize as *const (), b as usize as *const (), 4, 2) as u32
}
