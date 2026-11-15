#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f05: wrapping_/saturating_/overflowing_ families
#[inline(always)]
fn h(x: u128) -> u64 {
    (x as u64) ^ ((x >> 64) as u64).rotate_left(29)
}
#[no_mangle]
pub extern "C" fn wr_i8(a: i32, b: i32) -> u64 {
    let (x, y) = (a as i8, b as i8);
    let v = [
        x.wrapping_add(y),
        x.wrapping_sub(y),
        x.wrapping_mul(y),
        if y != 0 { x.wrapping_div(y) } else { 1 },
        if y != 0 { x.wrapping_rem(y) } else { 2 },
        x.wrapping_neg(),
        x.wrapping_abs(),
        x.wrapping_shl(b as u32),
        x.wrapping_shr(b as u32),
    ];
    let mut r = 0u64;
    let mut i = 0;
    while i < v.len() {
        let e = v[i];
        i += 1;
        r = r.wrapping_mul(1000003) ^ (e as u8 as u64);
    }
    r
}
#[no_mangle]
pub extern "C" fn sat_i8(a: i32, b: i32) -> u64 {
    let (x, y) = (a as i8, b as i8);
    let v = [
        x.saturating_add(y),
        x.saturating_sub(y),
        x.saturating_mul(y),
        x.saturating_neg(),
        x.saturating_abs(),
        x.saturating_pow(b as u32 & 7),
        if y != 0 { x.saturating_div(y) } else { 3 },
    ];
    let mut r = 0u64;
    let mut i = 0;
    while i < v.len() {
        let e = v[i];
        i += 1;
        r = r.wrapping_mul(1000003) ^ (e as u8 as u64);
    }
    r
}
#[no_mangle]
pub extern "C" fn sat_u16(a: i32, b: i32) -> u64 {
    let (x, y) = (a as u16, b as u16);
    let v = [
        x.saturating_add(y),
        x.saturating_sub(y),
        x.saturating_mul(y),
        x.saturating_pow(b as u32 & 15),
        x.saturating_add_signed(b as i16),
    ];
    let mut r = 0u64;
    let mut i = 0;
    while i < v.len() {
        let e = v[i];
        i += 1;
        r = r.wrapping_mul(1000003) ^ (e as u64);
    }
    r
}
#[no_mangle]
pub extern "C" fn ovf_i16(a: i32, b: i32) -> u64 {
    let (x, y) = (a as i16, b as i16);
    let v = [
        x.overflowing_add(y),
        x.overflowing_sub(y),
        x.overflowing_mul(y),
        x.overflowing_neg(),
        x.overflowing_abs(),
        x.overflowing_shl(b as u32),
        if y != 0 {
            x.overflowing_div(y)
        } else {
            (5, true)
        },
        if y != 0 {
            x.overflowing_rem(y)
        } else {
            (6, false)
        },
    ];
    let mut r = 0u64;
    let mut i = 0;
    while i < v.len() {
        let (e, o) = v[i];
        i += 1;
        r = r.wrapping_mul(1000003) ^ (e as u16 as u64) ^ ((o as u64) << 20);
    }
    r
}
#[no_mangle]
pub extern "C" fn ovf_u32(a: u32, b: u32) -> u64 {
    let v = [
        a.overflowing_add(b),
        a.overflowing_sub(b),
        a.overflowing_mul(b),
        a.overflowing_neg(),
        a.overflowing_shr(b),
        a.overflowing_add_signed(b as i32),
    ];
    let mut r = 0u64;
    let mut i = 0;
    while i < v.len() {
        let (e, o) = v[i];
        i += 1;
        r = r.wrapping_mul(1000003) ^ (e as u64) ^ ((o as u64) << 40);
    }
    r
}
#[no_mangle]
pub extern "C" fn sat_i32(a: i32, b: i32) -> u64 {
    let v = [
        a.saturating_add(b),
        a.saturating_sub(b),
        a.saturating_mul(b),
        a.saturating_neg(),
        a.saturating_abs(),
        a.saturating_pow(b as u32 & 31),
        if b != 0 { a.saturating_div(b) } else { 9 },
        a.saturating_add_unsigned(b as u32),
        a.saturating_sub_unsigned(b as u32),
    ];
    let mut r = 0u64;
    let mut i = 0;
    while i < v.len() {
        let e = v[i];
        i += 1;
        r = r.wrapping_mul(1000003) ^ (e as u32 as u64);
    }
    r
}
#[no_mangle]
pub extern "C" fn ovf_i64(a: i64, b: i64) -> u64 {
    let v = [
        a.overflowing_add(b),
        a.overflowing_sub(b),
        a.overflowing_mul(b),
        a.overflowing_neg(),
        a.overflowing_abs(),
        if b != 0 {
            a.overflowing_div(b)
        } else {
            (1, true)
        },
        if b != 0 {
            a.overflowing_rem_euclid(b)
        } else {
            (2, true)
        },
    ];
    let mut r = 0u64;
    let mut i = 0;
    while i < v.len() {
        let (e, o) = v[i];
        i += 1;
        r = r.rotate_left(13) ^ (e as u64) ^ (o as u64);
    }
    r
}
#[no_mangle]
pub extern "C" fn sat_u64(a: u64, b: u64) -> u64 {
    let v = [
        a.saturating_add(b),
        a.saturating_sub(b),
        a.saturating_mul(b),
        a.saturating_pow((b & 63) as u32),
        a.saturating_add_signed(b as i64),
    ];
    let mut r = 0u64;
    let mut i = 0;
    while i < v.len() {
        let e = v[i];
        i += 1;
        r = r.rotate_left(13) ^ e;
    }
    r
}
#[no_mangle]
pub extern "C" fn wr_u128(a: u64, b: u64) -> u64 {
    let x = ((a as u128) << 64) | (b as u128);
    let y = ((b as u128) << 64) | (!a as u128);
    let v = [
        x.wrapping_add(y),
        x.wrapping_sub(y),
        x.wrapping_mul(y),
        x.wrapping_neg(),
        x.wrapping_shl(b as u32),
        x.wrapping_shr(a as u32),
        x.saturating_add(y),
        x.saturating_sub(y),
        x.saturating_mul(y),
    ];
    let mut r = 0u64;
    let mut i = 0;
    while i < v.len() {
        let e = v[i];
        i += 1;
        r = r.rotate_left(13) ^ h(e);
    }
    r
}
#[no_mangle]
pub extern "C" fn sat_i128(a: i64, b: i64) -> u64 {
    let x = ((a as i128) << 64) | (b as u64 as i128);
    let y = (b as i128) << 1;
    let v = [
        x.saturating_add(y),
        x.saturating_sub(y),
        x.saturating_mul(y),
        x.saturating_neg(),
        x.wrapping_abs(),
        x.wrapping_shl(a as u32),
        x.wrapping_shr(b as u32),
        x.saturating_abs(),
        x.wrapping_neg(),
        x.wrapping_mul(y),
    ];
    let mut r = 0u64;
    let mut i = 0;
    while i < v.len() {
        let e = v[i];
        i += 1;
        r = r.rotate_left(13) ^ h(e as u128);
    }
    r
}
