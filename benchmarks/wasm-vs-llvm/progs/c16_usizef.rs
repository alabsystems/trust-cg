#![no_std]
#![allow(dead_code)]
#![feature(core_float_math, float_minimum_maximum)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
#[inline(never)]
fn lenf(s: &[u8]) -> f64 {
    s.len() as f64
}
#[no_mangle]
pub extern "C" fn len_f(k: u32) -> f64 {
    let b = [1u8; 40];
    lenf(&b[..(k % 41) as usize])
}
#[no_mangle]
pub extern "C" fn idx_sum(n: u32) -> f64 {
    let n = n % 100;
    let mut s = 0.0;
    let mut i: usize = 0;
    while i < n as usize {
        s += i as f64 * 0.5;
        i += 1;
    }
    s
}
#[no_mangle]
pub extern "C" fn isize_diff(a: u32, b: u32) -> f64 {
    (a as isize - b as isize) as f64
}
#[no_mangle]
pub extern "C" fn usize_big(a: u32, b: u32) -> f32 {
    (a as usize).wrapping_add(b as usize) as f32
}
#[no_mangle]
pub extern "C" fn f_to_idx(x: f64) -> u32 {
    let t = [3u32, 1, 4, 1, 5, 9, 2, 6];
    let i = x as usize;
    if i < 8 { t[i] } else { (i as u32) ^ 0xabc }
}
#[no_mangle]
pub extern "C" fn f_to_isize(x: f32) -> i32 {
    let i = x as isize;
    (i.wrapping_mul(3) >> 1) as i32
}
#[no_mangle]
pub extern "C" fn u8mem_f(k: u32) -> f32 {
    let a: [u8; 4] = [0, 128, 255, 7];
    let b: [i8; 4] = [0, -128, -1, 7];
    let i = (k % 4) as usize;
    a[i] as f32 * 1000.0 + b[i] as f32
}
#[no_mangle]
pub extern "C" fn i16mem_f(k: u32) -> f64 {
    let a: [i16; 4] = [0, -32768, -1, 32767];
    let b: [u16; 4] = [0, 32768, 65535, 1];
    let i = (k % 4) as usize;
    a[i] as f64 * 100000.0 + b[i] as f64
}
#[no_mangle]
pub extern "C" fn f_to_u8mem(x: f32) -> u32 {
    let mut a = [0u8; 4];
    a[0] = x as u8;
    a[1] = (x * 2.0) as u8;
    a[2] = (-x) as i8 as u8;
    a[3] = (x as i16) as u8;
    u32::from_le_bytes(a)
}
