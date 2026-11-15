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
use core::cmp::Ordering;
#[inline(never)]
fn ord(o: Option<Ordering>) -> i32 {
    match o {
        Some(Ordering::Less) => -1,
        Some(Ordering::Equal) => 0,
        Some(Ordering::Greater) => 1,
        None => 7,
    }
}
#[no_mangle]
pub extern "C" fn pcmp64(a: f64, b: f64) -> i32 {
    ord(a.partial_cmp(&b))
}
#[no_mangle]
pub extern "C" fn pcmp32(a: f32, b: f32) -> i32 {
    ord(a.partial_cmp(&b))
}
#[no_mangle]
pub extern "C" fn tcmp64(a: u64, b: u64) -> i32 {
    ord(Some(f64::from_bits(a).total_cmp(&f64::from_bits(b))))
}
#[no_mangle]
pub extern "C" fn tcmp32(a: u32, b: u32) -> i32 {
    ord(Some(f32::from_bits(a).total_cmp(&f32::from_bits(b))))
}
#[no_mangle]
pub extern "C" fn rels64(a: f64, b: f64) -> u32 {
    (a < b) as u32
        | ((a <= b) as u32) << 1
        | ((a > b) as u32) << 2
        | ((a >= b) as u32) << 3
        | ((a == b) as u32) << 4
        | ((a != b) as u32) << 5
        | ((!(a < b)) as u32) << 6
        | ((!(a >= b)) as u32) << 7
}
#[no_mangle]
pub extern "C" fn rels32(a: f32, b: f32) -> u32 {
    (a < b) as u32
        | ((a <= b) as u32) << 1
        | ((a > b) as u32) << 2
        | ((a >= b) as u32) << 3
        | ((a == b) as u32) << 4
        | ((a != b) as u32) << 5
        | ((!(a <= b)) as u32) << 6
        | ((!(a > b)) as u32) << 7
}
#[no_mangle]
pub extern "C" fn preds64(x: u64) -> u32 {
    let a = f64::from_bits(x);
    a.is_nan() as u32
        | (a.is_finite() as u32) << 1
        | (a.is_infinite() as u32) << 2
        | (a.is_sign_negative() as u32) << 3
        | (a.is_sign_positive() as u32) << 4
        | (a.is_normal() as u32) << 5
        | (a.is_subnormal() as u32) << 6
}
#[no_mangle]
pub extern "C" fn preds32(x: u32) -> u32 {
    let a = f32::from_bits(x);
    a.is_nan() as u32
        | (a.is_finite() as u32) << 1
        | (a.is_infinite() as u32) << 2
        | (a.is_sign_negative() as u32) << 3
        | (a.is_sign_positive() as u32) << 4
        | (a.is_normal() as u32) << 5
        | (a.is_subnormal() as u32) << 6
}
#[inline(never)]
fn cls(c: core::num::FpCategory) -> u32 {
    c as u32 * 10 + 1
}
#[no_mangle]
pub extern "C" fn classify64(x: u64) -> u32 {
    cls(f64::from_bits(x).classify())
}
#[no_mangle]
pub extern "C" fn classify32(x: u32) -> u32 {
    cls(f32::from_bits(x).classify())
}
