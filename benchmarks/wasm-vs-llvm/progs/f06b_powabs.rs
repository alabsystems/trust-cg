#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f06: pow / checked_pow / abs / unsigned_abs / signum / euclid
#[no_mangle]
pub extern "C" fn pow_u32(a: u32, b: u32) -> u32 {
    a.pow(b & 31)
}
#[no_mangle]
pub extern "C" fn pow_i8(a: i32, b: i32) -> i32 {
    (a as i8).pow(b as u32 & 7) as i32
}
#[no_mangle]
pub extern "C" fn cpow_i64(a: i64, b: i64) -> i64 {
    match a.checked_pow((b & 127) as u32) {
        Some(v) => v,
        None => -12345,
    }
}
#[no_mangle]
pub extern "C" fn pow_u64_wr(a: u64, b: u64) -> u64 {
    a.saturating_pow((b & 255) as u32)
}
#[no_mangle]
pub extern "C" fn abs_all(a: i32, b: i32) -> u64 {
    let x8 = a as i8;
    let x16 = a as i16;
    let xs = a as isize;
    (x8.unsigned_abs() as u64)
        | (x16.unsigned_abs() as u64) << 8
        | (a.unsigned_abs() as u64) << 24
            ^ (xs.unsigned_abs() as u64).rotate_left(40)
            ^ (x8.wrapping_abs() as u8 as u64) << 56
            ^ (b.abs_diff(a) as u64)
            ^ ((b as i8).abs_diff(x8) as u64) << 33
}
#[no_mangle]
pub extern "C" fn abs_trap(a: i32, b: i32) -> i32 {
    (a as i16).abs() as i32 + b.abs()
}
#[no_mangle]
pub extern "C" fn signum_all(a: i64, b: i64) -> i64 {
    (a.signum() * 3
        + (a as i32).signum() as i64 * 5
        + (a as i8).signum() as i64 * 7
        + (b as i16).signum() as i64 * 11
        + (b as isize).signum() as i64 * 13
        + ((a as i128) * (b as i128)).signum() as i64 * 17)
        ^ (a.is_negative() as i64) << 10
        ^ (b.is_positive() as i64) << 11
}
#[no_mangle]
pub extern "C" fn euclid_i32(a: i32, b: i32) -> i64 {
    if b == 0 || (a == i32::MIN && b == -1) {
        return 7;
    }
    (a.div_euclid(b) as i64) << 32 ^ (a.rem_euclid(b) as u32 as i64)
}
#[no_mangle]
pub extern "C" fn euclid_i8_16(a: i32, b: i32) -> i64 {
    let (x, y) = (a as i8, b as i8);
    let (p, q) = (a as i16, b as i16);
    let r1 = x.checked_div_euclid(y).map(|v| v as i64).unwrap_or(-999)
        + x.checked_rem_euclid(y)
            .map(|v| v as i64 * 1000)
            .unwrap_or(-9999);
    let r2 = p.checked_div_euclid(q).map(|v| v as i64).unwrap_or(-999)
        ^ p.checked_rem_euclid(q)
            .map(|v| v as i64 * 100000)
            .unwrap_or(-99999);
    r1 ^ (r2 << 20) ^ (x.wrapping_rem_euclid(if y == 0 { 1 } else { y }) as i64) << 50
}
#[no_mangle]
pub extern "C" fn euclid_i64(a: i64, b: i64) -> i64 {
    a.div_euclid(b) ^ a.rem_euclid(b).rotate_left(21) ^ (a as u64).div_euclid(b as u64) as i64
}
