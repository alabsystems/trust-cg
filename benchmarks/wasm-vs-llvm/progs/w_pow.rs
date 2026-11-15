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
pub extern "C" fn w_pow(a: i64, e: u32) -> i64 {
    let x = (a % 1000) as i128;
    let e = e % 20;
    let p = x.checked_pow(e).map(fold).unwrap_or(-1);
    let w = x.wrapping_pow(e + 3);
    let s = (x as u128).saturating_pow(e);
    let (o, f) = x.overflowing_pow(e + 5);
    p ^ fold(w).rotate_left(3) ^ fold(s as i128).rotate_left(6) ^ fold(o).rotate_left(9) ^ f as i64
}
