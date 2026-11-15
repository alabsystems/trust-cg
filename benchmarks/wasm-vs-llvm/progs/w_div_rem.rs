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
pub extern "C" fn w_div_rem(a: i64, b: i64) -> i64 {
    let x = mk(a, b);
    let y = mk(b >> 32, a | 1) >> (a as u32 & 100);
    let q = x.checked_div(y);
    let r = x.checked_rem(y);
    let uq = (x as u128).checked_div(y as u128);
    let ur = (x as u128).checked_rem(y as u128);
    let e = x.checked_div_euclid(y);
    fold(q.unwrap_or(3))
        ^ fold(r.unwrap_or(5)).rotate_left(7)
        ^ fold(uq.unwrap_or(11) as i128).rotate_left(13)
        ^ fold(ur.unwrap_or(17) as i128).rotate_left(19)
        ^ fold(e.unwrap_or(23)).rotate_left(31)
}
