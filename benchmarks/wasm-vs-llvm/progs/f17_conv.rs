#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f17: try_from across widths, NonZero, Wrapping/Saturating, parsing
use core::convert::TryFrom;
use core::num::{NonZeroI16, NonZeroU8, NonZeroU32, NonZeroU128, Wrapping};
#[inline(always)]
fn h(x: u128) -> u64 {
    (x as u64) ^ ((x >> 64) as u64).rotate_left(29)
}
#[no_mangle]
pub extern "C" fn tryfrom_small(a: i64) -> u64 {
    let r1 = match u8::try_from(a) {
        Ok(v) => v as u64,
        Err(_) => 300,
    };
    let r2 = match i8::try_from(a) {
        Ok(v) => v as u8 as u64,
        Err(_) => 301,
    };
    let r3 = match u16::try_from(a) {
        Ok(v) => v as u64,
        Err(_) => 70000,
    };
    let r4 = match i16::try_from(a) {
        Ok(v) => v as u16 as u64,
        Err(_) => 70001,
    };
    r1 | r2 << 9 | r3 << 18 | r4 << 35
}
#[no_mangle]
pub extern "C" fn tryfrom_word(a: i64) -> u64 {
    let r1 = match u32::try_from(a) {
        Ok(v) => v as u64,
        Err(_) => 1 << 33,
    };
    let r2 = match i32::try_from(a) {
        Ok(v) => v as u32 as u64,
        Err(_) => 1 << 34,
    };
    let r3 = match usize::try_from(a) {
        Ok(v) => v as u64,
        Err(_) => 1 << 35,
    };
    let r4 = match isize::try_from(a) {
        Ok(v) => v as usize as u64,
        Err(_) => 1 << 36,
    };
    let r5 = match u64::try_from(a) {
        Ok(v) => v,
        Err(_) => 1 << 37,
    };
    r1 ^ r2.rotate_left(1) ^ r3.rotate_left(2) ^ r4.rotate_left(3) ^ r5.rotate_left(4)
}
#[no_mangle]
pub extern "C" fn tryfrom_wide(a: i64, b: i64) -> u64 {
    let x = ((a as i128) << 64) | (b as u64 as i128);
    let r1 = match u64::try_from(x) {
        Ok(v) => v,
        Err(_) => 11,
    };
    let r2 = match i64::try_from(x) {
        Ok(v) => v as u64,
        Err(_) => 12,
    };
    let r3 = match u128::try_from(x) {
        Ok(v) => h(v),
        Err(_) => 13,
    };
    let r4 = match i128::try_from(x as u128) {
        Ok(v) => h(v as u128),
        Err(_) => 14,
    };
    let r5 = match u8::try_from(x) {
        Ok(v) => v as u64,
        Err(_) => 15,
    };
    let r6 = match usize::try_from(x as u128) {
        Ok(v) => v as u64,
        Err(_) => 16,
    };
    r1 ^ r2.rotate_left(1)
        ^ r3.rotate_left(2)
        ^ r4.rotate_left(3)
        ^ r5.rotate_left(4)
        ^ r6.rotate_left(5)
}
#[no_mangle]
pub extern "C" fn tryfrom_uns(a: i64) -> u64 {
    let u = a as u64;
    let r1 = match i8::try_from(u) {
        Ok(v) => v as u64,
        Err(_) => 3,
    };
    let r2 = match i64::try_from(u) {
        Ok(v) => v as u64,
        Err(_) => 4,
    };
    let r3 = match u32::try_from(u as usize) {
        Ok(v) => v as u64,
        Err(_) => 5,
    };
    let r4 = match i32::try_from(u as usize) {
        Ok(v) => v as u64,
        Err(_) => 6,
    };
    let r5 = match i16::try_from(u as u16) {
        Ok(v) => v as u64,
        Err(_) => 7,
    };
    r1 ^ r2.rotate_left(8) ^ r3.rotate_left(16) ^ r4.rotate_left(24) ^ r5.rotate_left(32)
}
#[no_mangle]
pub extern "C" fn nonzero(a: i64, b: i64) -> u64 {
    let n8 = NonZeroU8::new(a as u8);
    let n16 = NonZeroI16::new(b as i16);
    let n32 = NonZeroU32::new(a as u32);
    let n128 = NonZeroU128::new(((a as u128) << 64) | b as u64 as u128);
    let r1 = n8
        .map(|v| v.get() as u64 + v.leading_zeros() as u64 * 1000)
        .unwrap_or(99999);
    let r2 = n16
        .map(|v| v.get() as i64 as u64 ^ (v.trailing_zeros() as u64) << 40)
        .unwrap_or(77);
    let r3 = n32
        .and_then(|v| v.checked_add(b as u32))
        .map(|v| v.get() as u64)
        .unwrap_or(55);
    let r4 = n128
        .map(|v| h(v.get()) ^ v.leading_zeros() as u64)
        .unwrap_or(33);
    let r5 = core::mem::size_of::<Option<NonZeroU8>>() as u64
        + core::mem::size_of::<Option<NonZeroU128>>() as u64 * 100;
    r1 ^ r2.rotate_left(10) ^ r3.rotate_left(20) ^ r4.rotate_left(30) ^ r5.rotate_left(50)
}
#[no_mangle]
pub extern "C" fn wrapping_types(a: i64, b: i64) -> u64 {
    let x = Wrapping(a as u8) + Wrapping(b as u8) * Wrapping(3u8) - Wrapping(200u8);
    let y = Wrapping(a as i16) * Wrapping(b as i16) << 3;
    let z = -Wrapping(a as i128) * Wrapping(b as i128);
    let s = Wrapping(a as u32) >> (b as usize);
    x.0 as u64 ^ (y.0 as u16 as u64) << 8 ^ h(z.0 as u128).rotate_left(24) ^ (s.0 as u64) << 30
}
#[no_mangle]
pub extern "C" fn parse_ints(k: u32, m: u32) -> u64 {
    let src = [
        "0",
        "255",
        "256",
        "-128",
        "-129",
        "+7",
        "340282366920938463463374607431768211455",
        "340282366920938463463374607431768211456",
        "-170141183460469231731687303715884105728",
        "ffff",
        "7fffffff",
        "4294967295",
        "4294967296",
        "-1",
        "",
        "9223372036854775808",
    ];
    let s = src[(k % 16) as usize];
    let radix = [10u32, 16, 2, 36][(m % 4) as usize];
    let r1 = match u8::from_str_radix(s, radix) {
        Ok(v) => v as u64,
        Err(e) => 1000 + *e.kind() as u64,
    };
    let r2 = match i8::from_str_radix(s, radix) {
        Ok(v) => v as u8 as u64,
        Err(e) => 2000 + *e.kind() as u64,
    };
    let r3 = match u128::from_str_radix(s, radix) {
        Ok(v) => h(v),
        Err(e) => 3000 + *e.kind() as u64,
    };
    let r4 = match i128::from_str_radix(s, radix) {
        Ok(v) => h(v as u128),
        Err(e) => 4000 + *e.kind() as u64,
    };
    let r5 = match usize::from_str_radix(s, radix) {
        Ok(v) => v as u64,
        Err(e) => 5000 + *e.kind() as u64,
    };
    r1 ^ r2.rotate_left(11) ^ r3.rotate_left(22) ^ r4.rotate_left(33) ^ r5.rotate_left(44)
}
#[no_mangle]
pub extern "C" fn from_widen(a: i64) -> u64 {
    let x8 = a as u8;
    let y8 = a as i8;
    (u16::from(x8) as u64)
        ^ (i32::from(y8) as u32 as u64) << 16
        ^ (u64::from(x8)) << 48
        ^ h(u128::from(a as u64)).rotate_left(3)
        ^ h(i128::from(a) as u128).rotate_left(5)
        ^ (usize::from(x8) as u64) << 24
        ^ (isize::from(y8) as i64 as u64).rotate_left(7)
        ^ (i64::from(a as u32)) as u64
        ^ (f64::from(a as i32)).to_bits()
        ^ (u32::from(a < 0)) as u64
}
