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
use core::mem::transmute;
#[no_mangle]
pub extern "C" fn f2usize(x: f32) -> u32 {
    let u: usize = unsafe { transmute(x) };
    (u as u32) ^ ((u >> 3) as u32)
}
#[no_mangle]
pub extern "C" fn usize2f(x: u32) -> f32 {
    let f: f32 = unsafe { transmute(x as usize) };
    if f.is_nan() { 7.0 } else { f }
}
#[no_mangle]
pub extern "C" fn isize2f(x: i32) -> f64 {
    let f: f32 = unsafe { transmute((x as isize).wrapping_sub(1)) };
    if f.is_nan() { 7.0 } else { f as f64 }
}
union U {
    f: f32,
    u: usize,
}
#[no_mangle]
pub extern "C" fn uni(x: f32) -> u32 {
    let v = U { f: x };
    let w = unsafe { v.u };
    w.count_ones() * 1000 + (w >> 23) as u32
}
#[no_mangle]
pub extern "C" fn uni2(x: u32) -> f32 {
    let v = U { u: x as usize };
    let f = unsafe { v.f };
    if f.is_nan() { -7.0 } else { f * 2.0 }
}
#[no_mangle]
pub extern "C" fn bits_usize(x: f64) -> u32 {
    let b = x.to_bits();
    let u = b as usize;
    (u as u32) ^ ((b >> 32) as usize as u32)
}
#[no_mangle]
pub extern "C" fn usize_bits(x: u32, y: u32) -> f64 {
    let hi = x as usize;
    let lo = y as usize;
    let f = f64::from_bits(((hi as u64) << 32) | lo as u64);
    if f.is_nan() { 7.0 } else { f }
}
#[no_mangle]
pub extern "C" fn f32_ptr(x: f32) -> u32 {
    let p: *const f32 = &x;
    let q = p as usize;
    let r = unsafe { *(q as *const u32) };
    r ^ ((q & 3) as u32)
}
#[no_mangle]
pub extern "C" fn fsz(x: u32) -> u32 {
    (core::mem::size_of::<usize>() as u32) * 100 + core::mem::align_of::<f64>() as u32 * 10 + x % 7
}
