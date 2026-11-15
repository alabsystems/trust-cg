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
fn u8_ops(a: u8, b: u8) -> u32 {
    let r1 = a.rotate_left(b as u32) as u32;
    let r2 = a.leading_zeros() + b.trailing_zeros() * 16;
    let r3 = a.reverse_bits() as u32;
    let r4 = a.wrapping_shl(b as u32) as u32;
    let r5 = (a.wrapping_add(b) >> 1) as u32;
    let r6 = a.checked_shr(b as u32).map(|x| x as u32).unwrap_or(0x1ff);
    let r7 = a.abs_diff(b) as u32;
    let r8 = (a as i8).wrapping_mul(b as i8) as u32;
    let r9 = a.saturating_sub(b).count_ones() + (a as i8).leading_ones();
    r1 ^ r2 << 3 ^ r3 << 6 ^ r4 << 9 ^ r5 << 12 ^ r6 << 15 ^ r7 << 18 ^ r8 << 21 ^ r9 << 26
}

#[inline(never)]
fn i16_ops(a: i16, b: i16) -> i64 {
    let r1 = a.wrapping_mul(b) as i64;
    let r2 = a.rotate_right(b as u32) as i64;
    let r3 = a.swap_bytes() as i64;
    let r4 = (a >> (b & 15)) as i64;
    let r5 = a.wrapping_div(if b == 0 { 1 } else { b }) as i64;
    let r6 = a.checked_rem_euclid(b).map(|v| v as i64).unwrap_or(77);
    let r7 = a.leading_zeros() as i64 + a.count_zeros() as i64 * 32;
    let r8 = (a as u16 >> 3) as i64;
    let r9 = a.overflowing_neg().0 as i64 + a.overflowing_neg().1 as i64;
    let r10 = a.saturating_add(b) as i64;
    r1 ^ r2 << 8
        ^ r3 << 16
        ^ r4 << 24
        ^ r5 << 32
        ^ r6 << 40
        ^ r7 << 44
        ^ r8 << 50
        ^ r9 << 3
        ^ r10 << 11
}

#[inline(never)]
fn i8_signed(a: i8, b: i8) -> i32 {
    let s = (a as i32) + (b as i32);
    let c = a.wrapping_add(b) as i32;
    let d = (a / if b == 0 { 1 } else { b }) as i32;
    let e = a.checked_div(b).map(|x| x as i32).unwrap_or(1000);
    let f = (a as u8 as i32) - (b as u8 as i32);
    let g = (a.wrapping_abs() as u8) as i32;
    let h = (a < b) as i32 + ((a as u8) < (b as u8)) as i32 * 2;
    let i = a.pow((b & 3) as u32) as i32;
    s ^ c << 4 ^ d << 8 ^ e << 12 ^ f << 16 ^ g << 20 ^ h << 28 ^ i << 2
}

#[inline(never)]
fn swap_mixed(
    a: &mut [u16; 9],
    b: &mut [(u8, u32); 4],
    c: &mut [f64; 3],
    i: usize,
    j: usize,
) -> u64 {
    a.swap(i % 9, j % 9);
    b.swap(i % 4, j % 4);
    c.swap(i % 3, j % 3);
    {
        let (l, r) = a.split_at_mut(4);
        core::mem::swap(&mut l[0], &mut r[4]);
    }
    let t = core::mem::replace(&mut b[0], (7, 7));
    b[3] = t;
    let mut h = 0u64;
    for &x in a.iter() {
        h = h * 31 + x as u64;
    }
    for &(p, q) in b.iter() {
        h = h * 37 + p as u64 * 65536 + q as u64;
    }
    for &f in c.iter() {
        h = h.rotate_left(9) ^ f.to_bits();
    }
    h
}

#[inline(never)]
fn swap_wide(a: &mut [u128; 5], b: &mut [i64; 4], i: usize, j: usize) -> u64 {
    a.swap(i % 5, j % 5);
    b.swap(i % 4, j % 4);
    {
        let (l, r) = a.split_at_mut(2);
        core::mem::swap(&mut l[1], &mut r[1]);
    }
    let v = core::mem::take(&mut b[2]);
    b[0] = b[0].wrapping_add(v);
    let mut h = 0u64;
    for x in a.iter() {
        h = h.rotate_left(11) ^ (*x as u64) ^ ((*x >> 64) as u64);
    }
    for x in b.iter() {
        h = h.rotate_left(5) ^ (*x as u64);
    }
    h
}

#[derive(Clone, Copy)]
struct Px {
    r: u8,
    g: u8,
    b: u8,
    a: u8,
}

#[inline(never)]
fn blend(p: Px, q: Px) -> Px {
    let al = q.a as u16;
    let inv = 255 - al;
    Px {
        r: ((p.r as u16 * inv + q.r as u16 * al + 127) / 255) as u8,
        g: ((p.g as u16 * inv + q.g as u16 * al + 127) / 255) as u8,
        b: ((p.b as u16 * inv + q.b as u16 * al + 127) / 255) as u8,
        a: p.a.max(q.a),
    }
}

#[no_mangle]
pub extern "C" fn u16_checksum(seed: u32, n: u32) -> u32 {
    let mut words = [0u16; 40];
    let mut s = seed;
    for w in words.iter_mut() {
        s = s.wrapping_mul(1664525).wrapping_add(1013904223);
        *w = (s >> 16) as u16;
    }
    let n = (n % 41) as usize;
    let mut sum: u32 = 0;
    for &w in &words[..n] {
        sum += w as u32;
    }
    while sum >> 16 != 0 {
        sum = (sum & 0xffff) + (sum >> 16);
    }
    let fl = !(sum as u16);
    let mut f1 = 0u16;
    let mut f2 = 0u16;
    for &w in &words[..n] {
        f1 = ((f1 as u32 + (w & 0xff) as u32) % 255) as u16;
        f2 = ((f2 as u32 + f1 as u32) % 255) as u16;
    }
    (fl as u32) << 16 | (f2 << 8 | f1) as u32
}
