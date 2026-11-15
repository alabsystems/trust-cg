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

#[no_mangle]
pub extern "C" fn w_float_conv(a: i64, b: i64) -> f64 {
    let x = mk(a >> 20, b);
    let f1 = (x >> 64) as i64 as f64;
    let f2 = (x as u64) as f64;
    let f3 = (x >> 40) as i64 as f32 as f64;
    f1 * 18446744073709551616.0 + f2 - f3
}

#[no_mangle]
pub extern "C" fn w_from_float(f: f64, g: f64) -> i64 {
    let a = f as i128;
    let b = (f * g) as u128;
    let c = (f * 1e20) as i128;
    let d = (g as f32) as u128;
    fold(a)
        ^ fold(b as i128).rotate_left(1)
        ^ fold(c).rotate_left(2)
        ^ fold(d as i128).rotate_left(3)
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

#[no_mangle]
pub extern "C" fn w_div_rem(a: i64, b: i64) -> i64 {
    let x = mk(a, b);
    let y = mk(b >> 32, a | 1) >> (a as u32 & 100);
    if y == 0 || (x == i128::MIN && y == -1) {
        return -99;
    }
    let q = x / y;
    let r = x % y;
    let uq = (x as u128) / (y as u128);
    let ur = (x as u128) % (y as u128);
    let e = x.div_euclid(y);
    let re = x.rem_euclid(y);
    fold(q)
        ^ fold(r).rotate_left(7)
        ^ fold(uq as i128).rotate_left(13)
        ^ fold(ur as i128).rotate_left(19)
        ^ fold(e).rotate_left(31)
        ^ fold(re).rotate_left(37)
}

#[no_mangle]
pub extern "C" fn w_shifts(a: i64, b: i64) -> i64 {
    let x = mk(a, b);
    let s = (b as u32) & 127;
    let l = x << s;
    let r = x >> s;
    let ur = (x as u128) >> s;
    let rl = (x as u128).rotate_left(a as u32);
    let rr = x.rotate_right(b as u32);
    fold(l)
        ^ fold(r).rotate_left(3)
        ^ fold(ur as i128).rotate_left(5)
        ^ fold(rl as i128).rotate_left(9)
        ^ fold(rr).rotate_left(11)
}

#[no_mangle]
pub extern "C" fn w_bits(a: i64, b: i64) -> i64 {
    let x = mk(a, b);
    let u = x as u128;
    (u.leading_zeros() as i64)
        | (u.trailing_zeros() as i64) << 8
        | (u.count_ones() as i64) << 16
        | (x.leading_ones() as i64) << 24
        | ((u.swap_bytes() >> 100) as i64) << 32
        | ((u.reverse_bits() & 0xff) as i64) << 48
        | ((x.is_negative() as i64) << 62)
}

#[no_mangle]
pub extern "C" fn w_pow(a: i64, e: u32) -> i64 {
    let x = (a % 1000) as i128;
    let e = e % 20;
    let p = match x.checked_pow(e) {
        Some(v) => fold(v),
        None => -1,
    };
    let w = x.wrapping_pow(e + 3);
    let s = (x as u128).saturating_pow(e);
    let (o, f) = x.overflowing_pow(e + 5);
    p ^ fold(w).rotate_left(3) ^ fold(s as i128).rotate_left(6) ^ fold(o).rotate_left(9) ^ f as i64
}

#[no_mangle]
pub extern "C" fn w_cmp(a: i64, b: i64) -> i32 {
    let x = mk(a, b);
    let y = mk(b, a);
    let mut r = 0;
    if x < y {
        r |= 1;
    }
    if (x as u128) < (y as u128) {
        r |= 2;
    }
    if x == y {
        r |= 4;
    }
    if x.max(y) == x {
        r |= 8;
    }
    if (x as u128).min(y as u128) == y as u128 {
        r |= 16;
    }
    r |= (x.cmp(&y) as i32 + 1) << 5;
    r |= ((x.abs_diff(y) >> 120) as i32) << 8;
    r
}

#[no_mangle]
pub extern "C" fn w_mul_wide(a: u64, b: u64) -> u64 {
    let p = a as u128 * b as u128;
    let q = (a as i64 as i128) * (b as i64 as i128);
    let s = p.wrapping_add(q as u128).wrapping_sub((a as u128) << 64);
    (s >> 64) as u64 ^ s as u64 ^ (p >> 96) as u64
}
