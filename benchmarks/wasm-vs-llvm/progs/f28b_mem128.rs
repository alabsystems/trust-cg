#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f28: 128-bit values in memory (arrays, struct fields, by-ref params)
#[inline(always)]
fn h(x: u128) -> u64 {
    (x as u64) ^ ((x >> 64) as u64).rotate_left(29)
}
#[derive(Clone, Copy)]
struct W {
    a: u8,
    x: u128,
    b: u16,
    y: i128,
    c: u32,
}
#[inline(never)]
fn bump(w: &mut W, k: u64) {
    w.x = w.x.wrapping_mul(k as u128 | 1).rotate_left(k as u32);
    w.y = w.y.wrapping_sub(w.x as i128) >> 3;
    w.a = w.a.wrapping_add(k as u8);
    w.b ^= w.x as u16;
    w.c = w.c.wrapping_mul(w.y as u32);
}
#[no_mangle]
pub extern "C" fn mem_struct(a: i64, b: i64) -> u64 {
    let mut w = W {
        a: a as u8,
        x: ((a as u128) << 64) | b as u64 as u128,
        b: b as u16,
        y: -((b as i128) << 70),
        c: a as u32,
    };
    let mut i = 0;
    while i < 5 {
        bump(&mut w, (a as u64).wrapping_add(i));
        i += 1;
    }
    h(w.x) ^ h(w.y as u128).rotate_left(3) ^ (w.a as u64) << 56 ^ (w.b as u64) << 40 ^ (w.c as u64)
}
#[no_mangle]
pub extern "C" fn mem_array(a: i64, b: i64) -> u64 {
    let mut v = [0u128; 6];
    let mut s = [0i128; 6];
    let mut i = 0usize;
    while i < 6 {
        v[i] = ((a as u128) << (i * 20)) ^ (b as u64 as u128).wrapping_mul(i as u128 + 1);
        s[i] = (v[i] as i128).wrapping_neg() >> i;
        i += 1;
    }
    i = 1;
    while i < 6 {
        v[i] = v[i].wrapping_add(v[i - 1]);
        s[i] = s[i].wrapping_mul(s[i - 1] | 1);
        i += 1;
    }
    let mut r = 0u64;
    i = 0;
    while i < 6 {
        r = r.rotate_left(11)
            ^ h(v[i])
            ^ h(s[i] as u128)
            ^ ((v[i] > s[i] as u128) as u64)
            ^ ((s[i] < 0) as u64) << 1;
        i += 1;
    }
    r
}
#[inline(never)]
fn by_ref(x: &u128, y: &mut i128, z: &[u128]) -> u128 {
    *y = y.wrapping_add(*x as i128);
    z.iter().fold(*x, |acc, &e| acc.wrapping_mul(3) ^ e)
}
#[no_mangle]
pub extern "C" fn mem_ref(a: i64, b: i64) -> u64 {
    let x = ((a as u128) << 64) | b as u64 as u128;
    let mut y = (b as i128) << 64;
    let z = [x, !x, x >> 3, x << 5];
    let r = by_ref(&x, &mut y, &z[(a as u64 % 3) as usize..]);
    h(r) ^ h(y as u128).rotate_left(7)
}
#[no_mangle]
pub extern "C" fn mem_sort(a: i64, b: i64) -> u64 {
    let mut v = [
        ((a as i128) << 64) | b as u64 as i128,
        -(a as i128),
        (b as i128) << 100,
        i128::MIN,
        i128::MAX,
        0,
        a as i128 * b as i128,
    ];
    let mut i = 1;
    while i < v.len() {
        let mut j = i;
        while j > 0 && v[j - 1] > v[j] {
            let t = v[j - 1];
            v[j - 1] = v[j];
            v[j] = t;
            j -= 1;
        }
        i += 1;
    }
    let mut r = 0u64;
    i = 0;
    while i < v.len() {
        r = r.rotate_left(9) ^ h(v[i] as u128);
        i += 1;
    }
    r
}
