#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f24: wide/narrow integers across call boundaries (params, returns, fn pointers, recursion)
#[inline(always)]
fn h(x: u128) -> u64 {
    (x as u64) ^ ((x >> 64) as u64).rotate_left(29)
}
#[inline(never)]
fn many(a: u128, b: i8, c: i128, d: u16, e: u64, f: i128, g: u8, k: usize, m: u128) -> u128 {
    a.wrapping_mul(3)
        ^ (b as u128)
        ^ (c as u128).rotate_left(5)
        ^ (d as u128) << 70
        ^ (e as u128) << 1
        ^ (f as u128).wrapping_neg()
        ^ (g as u128) << 120
        ^ (k as u128) << 90
        ^ m.swap_bytes()
}
#[no_mangle]
pub extern "C" fn call_many(a: i64, b: i64) -> u64 {
    let x = ((a as u128) << 64) | b as u64 as u128;
    h(many(
        x,
        a as i8,
        -(x as i128),
        b as u16,
        a as u64,
        (b as i128) << 100,
        (a >> 3) as u8,
        b as usize,
        !x,
    ))
}
#[inline(never)]
fn ret_pair(a: i64) -> (u128, i8) {
    (
        ((a as u128) << 64) | (a as u64 as u128 * 7),
        (a as i8).wrapping_neg(),
    )
}
#[inline(never)]
fn ret_tri(a: i64) -> (u8, u128, u16) {
    (
        a as u8,
        (a as u128).wrapping_mul(u128::MAX / 3),
        (a >> 8) as u16,
    )
}
#[no_mangle]
pub extern "C" fn call_rets(a: i64) -> u64 {
    let (x, y) = ret_pair(a);
    let (p, q, r) = ret_tri(a);
    h(x) ^ (y as u8 as u64) ^ (p as u64) << 8 ^ h(q).rotate_left(3) ^ (r as u64) << 40
}
fn f1(x: u128, y: i16) -> u128 {
    x.wrapping_add(y as u128)
}
fn f2(x: u128, y: i16) -> u128 {
    x.wrapping_mul(y as i128 as u128)
}
fn f3(x: u128, y: i16) -> u128 {
    x.rotate_right(y as u32)
}
#[no_mangle]
pub extern "C" fn call_fnptr(a: i64, b: i64) -> u64 {
    let fs: [fn(u128, i16) -> u128; 3] = [f1, f2, f3];
    let x = ((a as u128) << 64) | b as u64 as u128;
    let f = fs[(b as u64 % 3) as usize];
    h(f(f(x, a as i16), b as i16))
}
#[inline(never)]
fn fact(n: u32) -> u128 {
    if n <= 1 {
        1
    } else {
        (n as u128).wrapping_mul(fact(n - 1))
    }
}
#[inline(never)]
fn gcd(a: u128, b: u128) -> u128 {
    if b == 0 { a } else { gcd(b, a % b) }
}
#[no_mangle]
pub extern "C" fn call_rec(a: i64, b: i64) -> u64 {
    let n = (a as u64 % 40) as u32;
    h(fact(n))
        ^ h(gcd(
            ((a as u128) << 64) | 12345,
            ((b as u64 as u128) << 17) | 3,
        ))
        .rotate_left(7)
}
#[no_mangle]
pub extern "C" fn call_closure(a: i64, b: i64) -> u64 {
    let base = ((a as i128) << 64) - b as i128;
    let add = |x: i128, y: i8| -> i128 { x.wrapping_add(y as i128).wrapping_add(base) };
    let mul = move |x: u16| -> u128 { (x as u128) * (base as u128) };
    h(add(base, a as i8) as u128) ^ h(mul(b as u16)).rotate_left(9)
}
#[inline(never)]
fn narrow_ret_u8(a: u32) -> u8 {
    (a as u8).wrapping_mul(201)
}
#[inline(never)]
fn narrow_ret_i16(a: u32) -> i16 {
    (a as i16).wrapping_sub(30000)
}
#[inline(never)]
fn bool_ret(a: u32) -> bool {
    a.count_ones() % 2 == 1
}
#[no_mangle]
pub extern "C" fn call_narrow(a: u32) -> u64 {
    let x = narrow_ret_u8(a);
    let y = narrow_ret_i16(a);
    let z = bool_ret(a);
    (x as u64)
        | (y as i64 as u64) << 8
            ^ (z as u64) << 63
            ^ ((x > 100) as u64) << 62
            ^ ((y < 0) as u64) << 61
            ^ (x.wrapping_add(x) as u64) << 40
}
