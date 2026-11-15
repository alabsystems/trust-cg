#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f03: u128/i128 arithmetic near 2^64 (debug overflow checks)
#[inline(always)]
fn h(x: u128) -> u64 {
    (x as u64) ^ ((x >> 64) as u64).rotate_left(29)
}
#[no_mangle]
pub extern "C" fn u128_mul_near64(a: u64, b: u64) -> u64 {
    // operands straddle 2^64
    let x = (1u128 << 64) + a as u128;
    let y = (1u128 << 64) - (b as u128 | 1);
    h(x.wrapping_mul(y))
        ^ match x.checked_mul(y) {
            Some(v) => h(v),
            None => 7,
        }
}
#[no_mangle]
pub extern "C" fn u128_div_near64(a: u64, b: u64) -> u64 {
    let x = ((a as u128) << 64) | b as u128;
    let d = (b as u128) + (1u128 << 64) - 1;
    h(x / d) ^ h(x % d)
}
#[no_mangle]
pub extern "C" fn u128_div_small(a: u64, b: u64) -> u64 {
    let x = ((a as u128) << 64) | (a ^ b) as u128;
    let d = b as u128;
    h(x / d) ^ h(x % d).rotate_left(3)
}
#[no_mangle]
pub extern "C" fn u128_div4(a: u64, b: u64, c: u64, d: u64) -> u64 {
    let x = ((a as u128) << 64) | b as u128;
    let y = ((c as u128) << 64) | d as u128;
    if y == 0 {
        return 99;
    }
    h(x / y) ^ h(x % y).rotate_left(11)
}
#[no_mangle]
pub extern "C" fn i128_div4(a: i64, b: u64, c: i64, d: u64) -> u64 {
    let x = (((a as i128) << 64) | b as i128) as i128;
    let y = (((c as i128) << 64) | d as i128) as i128;
    match (x.checked_div(y), x.checked_rem(y)) {
        (Some(q), Some(r)) => h(q as u128) ^ h(r as u128).rotate_left(7),
        _ => 12345,
    }
}
#[no_mangle]
pub extern "C" fn i128_mul_trap(a: i64, b: i64) -> u64 {
    let x = (a as i128) << 63;
    let y = b as i128;
    h((x * y) as u128)
}
#[no_mangle]
pub extern "C" fn u128_add_trap(a: u64, b: u64) -> u64 {
    let x = u128::MAX - a as u128;
    h(x + b as u128)
}
#[no_mangle]
pub extern "C" fn i128_sub_trap(a: i64, b: i64) -> u64 {
    let x = i128::MIN + (a as i128);
    h((x - b as i128) as u128)
}
#[no_mangle]
pub extern "C" fn i128_div_trap(a: i64, b: i64) -> u64 {
    let x = if a == 0 { i128::MIN } else { (a as i128) << 64 };
    h((x / b as i128) as u128) ^ h((x % (b as i128)) as u128)
}
#[no_mangle]
pub extern "C" fn i128_signed_div(a: i64, b: i64) -> u64 {
    let x = ((a as i128) << 64) - (b as i128);
    let y = (b as i128) * 3 + 1;
    let q = if y == -1 { x.wrapping_neg() } else { x / y };
    let r = if y == -1 { 0 } else { x % y };
    h(q as u128) ^ h(r as u128) ^ ((q * y + r == x) as u64)
}
