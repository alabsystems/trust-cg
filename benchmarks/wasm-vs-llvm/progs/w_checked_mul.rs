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
pub extern "C" fn w_checked_mul(a: i64, b: i64) -> i64 {
    let x = mk(a, b) >> (b as u32 & 63);
    let y = mk(b, a) >> (a as u32 & 127);
    match x.checked_mul(y) {
        Some(p) => fold(p),
        None => match (x as u128).checked_mul(y as u128) {
            Some(q) => fold(q as i128) ^ 1,
            None => -7,
        },
    }
}
