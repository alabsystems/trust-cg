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
fn mk(a: i64, b: i64) -> i128 {
    ((a as i128) << 64) ^ (b as u64 as i128)
}

#[inline(never)]
fn fold(x: i128) -> i64 {
    (x as i64) ^ ((x >> 64) as i64).rotate_left(29)
}

#[inline(never)]
fn parse_u128(s: &str) -> Option<u128> {
    let mut v: u128 = 0;
    for c in s.bytes() {
        let d = (c as char).to_digit(10)? as u128;
        v = v.checked_mul(10)?.checked_add(d)?;
    }
    Some(v)
}

#[no_mangle]
pub extern "C" fn w_mul_wide(a: u64, b: u64) -> u64 {
    let p = a as u128 * b as u128;
    let q = (a as i64 as i128) * (b as i64 as i128);
    let s = p.wrapping_add(q as u128).wrapping_sub((a as u128) << 64);
    (s >> 64) as u64 ^ s as u64 ^ (p >> 96) as u64
}
