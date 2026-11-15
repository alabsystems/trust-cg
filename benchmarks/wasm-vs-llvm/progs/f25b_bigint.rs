#![feature(widening_mul, signed_bigint_helpers, const_unsigned_bigint_helpers)]
#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f25: nightly bigint helpers (carrying/borrowing/widening) across widths
#[inline(always)]
fn h(x: u128) -> u64 {
    (x as u64) ^ ((x >> 64) as u64).rotate_left(29)
}
#[no_mangle]
pub extern "C" fn carry_i16(a: i32, b: i32) -> u32 {
    let (x, y) = (a as i16, b as i16);
    let (s, c) = x.carrying_add(y, (a & 1) != 0);
    let (d, bo) = x.borrowing_sub(y, (b & 1) != 0);
    (s as u16 as u32) | (c as u32) << 16 | (d as u16 as u32) << 17 ^ (bo as u32) << 31
}
#[no_mangle]
pub extern "C" fn carry_u32(a: u32, b: u32) -> u64 {
    let (s, c) = a.carrying_add(b, (a & 1) != 0);
    let (d, bo) = a.borrowing_sub(b, (b & 1) != 0);
    let w = a.widening_mul(b);
    let (lo, hi) = (w as u32, (w >> 32) as u32);
    let (clo, chi) = a.carrying_mul(b, a ^ b);
    (s as u64)
        ^ (c as u64) << 32
        ^ (d as u64).rotate_left(33)
        ^ (bo as u64) << 63
        ^ (lo as u64).rotate_left(7)
        ^ (hi as u64).rotate_left(11)
        ^ (clo as u64).rotate_left(13)
        ^ (chi as u64).rotate_left(17)
}
#[no_mangle]
pub extern "C" fn carry_u64(a: u64, b: u64) -> u64 {
    let (s, c) = a.carrying_add(b, (a & 1) != 0);
    let (d, bo) = a.borrowing_sub(b, (b & 1) != 0);
    let w = a.widening_mul(b);
    let (lo, hi) = (w as u64, (w >> 64) as u64);
    let (clo, chi) = a.carrying_mul(b, a ^ b);
    let (alo, ahi) = a.carrying_mul_add(b, a, b);
    s ^ (c as u64)
        ^ d.rotate_left(3)
        ^ (bo as u64) << 1
        ^ lo.rotate_left(7)
        ^ hi.rotate_left(11)
        ^ clo.rotate_left(13)
        ^ chi.rotate_left(17)
        ^ alo.rotate_left(19)
        ^ ahi.rotate_left(23)
}
#[no_mangle]
pub extern "C" fn carry_i64(a: i64, b: i64) -> u64 {
    let (s, c) = a.carrying_add(b, (a & 1) != 0);
    let (d, bo) = a.borrowing_sub(b, (b & 1) != 0);
    (s as u64) ^ (c as u64) ^ (d as u64).rotate_left(3) ^ (bo as u64) << 1
}
#[no_mangle]
pub extern "C" fn carry_u128(a: i64, b: i64) -> u64 {
    let x = ((a as u128) << 64) | b as u64 as u128;
    let y = !x ^ (b as u128);
    let (s, c) = x.carrying_add(y, (a & 1) != 0);
    let (d, bo) = x.borrowing_sub(y, (b & 1) != 0);
    h(s) ^ (c as u64) ^ h(d).rotate_left(3) ^ (bo as u64) << 1
}
#[no_mangle]
pub extern "C" fn carry_usize(a: u32, b: u32) -> u64 {
    let (x, y) = (a as usize, b as usize);
    let (s, c) = x.carrying_add(y, (a & 1) != 0);
    let (lo, hi) = (x, y);
    let (clo, chi) = x.carrying_mul(y, x);
    (s as u64)
        ^ (c as u64) << 32
        ^ (lo as u64).rotate_left(7)
        ^ (hi as u64).rotate_left(11)
        ^ (clo as u64).rotate_left(13)
        ^ (chi as u64).rotate_left(17)
}
