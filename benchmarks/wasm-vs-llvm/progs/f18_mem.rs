#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f18: memory-backed integer arithmetic (struct fields, arrays, statics) incl. compound assignment with overflow checks
#[derive(Clone, Copy)]
struct S {
    a: u8,
    b: i16,
    c: u32,
    d: i64,
    e: u128,
    f: i8,
    g: usize,
}
static mut G8: u8 = 250;
static mut G128: i128 = i128::MAX - 3;
static mut GUS: usize = usize::MAX - 2;
#[inline(never)]
fn mk(a: i64, b: i64) -> S {
    S {
        a: a as u8,
        b: b as i16,
        c: a as u32,
        d: b,
        e: ((a as u128) << 64) | b as u64 as u128,
        f: b as i8,
        g: a as usize,
    }
}
#[inline(never)]
fn fold(s: &S) -> u64 {
    (s.a as u64)
        ^ (s.b as u16 as u64) << 8
        ^ (s.c as u64) << 24
        ^ (s.d as u64).rotate_left(7)
        ^ (s.e as u64)
        ^ ((s.e >> 64) as u64).rotate_left(13)
        ^ (s.f as u8 as u64) << 56
        ^ (s.g as u64).rotate_left(40)
}
#[no_mangle]
pub extern "C" fn field_add_trap(a: i64, b: i64) -> u64 {
    let mut s = mk(a, b);
    s.a += s.f as u8;
    s.b -= 7;
    s.c *= 3;
    s.d += a;
    s.f -= 1;
    s.g += 2;
    fold(&s)
}
#[no_mangle]
pub extern "C" fn field_u128_trap(a: i64, b: i64) -> u64 {
    let mut s = mk(a, b);
    s.e += (b as u64 as u128) << 60;
    s.e *= 3;
    fold(&s)
}
#[no_mangle]
pub extern "C" fn field_wrap(a: i64, b: i64) -> u64 {
    let mut s = mk(a, b);
    s.a = s.a.wrapping_mul(s.f as u8);
    s.b = s.b.wrapping_shl(a as u32);
    s.c = s.c.rotate_right(b as u32);
    s.d = s.d.wrapping_neg();
    s.e = s.e.wrapping_mul(s.e | 1);
    s.f = s.f.wrapping_abs();
    s.g = s.g.wrapping_sub(b as usize);
    fold(&s)
}
#[no_mangle]
pub extern "C" fn arr_narrow(a: i32, b: i32) -> u64 {
    let mut v = [0u8; 16];
    let mut w = [0i16; 8];
    let mut i = 0usize;
    while i < 16 {
        v[i] = (a as u8).wrapping_mul(i as u8).wrapping_add(b as u8);
        i += 1;
    }
    i = 0;
    while i < 8 {
        w[i] = (v[i * 2] as i16)
            .wrapping_sub(v[i * 2 + 1] as i16)
            .wrapping_mul(b as i16);
        i += 1;
    }
    let mut r = 0u64;
    i = 0;
    while i < 8 {
        r = r.rotate_left(9)
            ^ (w[i] as u16 as u64)
            ^ ((w[i] >> 3) as i64 as u64) << 20
            ^ (v[i] / (v[15 - i] | 1)) as u64;
        i += 1;
    }
    r
}
#[no_mangle]
pub extern "C" fn arr_add_trap(a: i32, b: i32) -> u32 {
    let mut v = [a as u8, b as u8, 200, 55];
    v[(b & 3) as usize] += v[(a & 3) as usize];
    v[0] as u32 | (v[1] as u32) << 8 | (v[2] as u32) << 16 | (v[3] as u32) << 24
}
#[no_mangle]
pub extern "C" fn static_u8(a: i32) -> u32 {
    unsafe {
        G8 = G8.wrapping_add(a as u8);
        G8 as u32
    }
}
#[no_mangle]
pub extern "C" fn static_u8_trap(a: i32) -> u32 {
    unsafe {
        G8 += (a as u8) & 3;
        G8 as u32
    }
}
#[no_mangle]
pub extern "C" fn static_i128(a: i64) -> u64 {
    unsafe {
        G128 = G128.wrapping_add(a as i128);
        (G128 as u64) ^ ((G128 >> 64) as u64)
    }
}
#[no_mangle]
pub extern "C" fn static_i128_trap(a: i64) -> u64 {
    unsafe {
        G128 -= (a as i128) << 100;
        (G128 as u64) ^ ((G128 >> 64) as u64)
    }
}
#[no_mangle]
pub extern "C" fn static_usize_trap(a: u32) -> u32 {
    unsafe {
        GUS += (a & 1) as usize;
        GUS as u32
    }
}
