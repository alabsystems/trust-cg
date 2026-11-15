#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f19: MIN / -1 edges for every signed width + newer integer APIs
#[no_mangle]
pub extern "C" fn minneg1_i32(a: i32, b: i32) -> u64 {
    let (q, o) = a.overflowing_div(if b == 0 { 1 } else { b });
    let (r, p) = a.overflowing_rem(if b == 0 { 1 } else { b });
    (q as u32 as u64)
        ^ (r as u32 as u64) << 32
        ^ (o as u64) << 1
        ^ (p as u64) << 2
        ^ (if b != 0 {
            a.wrapping_div(b)
                ^ a.wrapping_rem(b).rotate_left(5)
                ^ a.wrapping_div_euclid(b)
                ^ a.wrapping_rem_euclid(b)
        } else {
            0
        }) as u32 as u64
}
#[no_mangle]
pub extern "C" fn minneg1_i64(a: i64, b: i64) -> u64 {
    if b == 0 {
        return 5;
    }
    (a.wrapping_div(b) as u64)
        ^ (a.wrapping_rem(b) as u64).rotate_left(5)
        ^ (a.wrapping_div_euclid(b) as u64).rotate_left(9)
        ^ (a.wrapping_rem_euclid(b) as u64).rotate_left(13)
        ^ (a.checked_div(b).is_none() as u64)
        ^ (a.saturating_div(b) as u64).rotate_left(17)
}
#[no_mangle]
pub extern "C" fn minneg1_small(a: i32, b: i32) -> u64 {
    let (x8, y8) = (a as i8, b as i8);
    let (x16, y16) = (a as i16, b as i16);
    let (xs, ys) = (a as isize, b as isize);
    let y8 = if y8 == 0 { -1 } else { y8 };
    let y16 = if y16 == 0 { -1 } else { y16 };
    let ys = if ys == 0 { -1 } else { ys };
    (x8.wrapping_div(y8) as u8 as u64)
        ^ (x8.wrapping_rem(y8) as u8 as u64) << 8
        ^ (x16.wrapping_div(y16) as u16 as u64) << 16
        ^ (x16.wrapping_rem_euclid(y16) as u16 as u64) << 32
        ^ (xs.wrapping_div(ys) as usize as u64).rotate_left(40)
        ^ (x8.overflowing_div_euclid(y8).1 as u64) << 63
        ^ (xs.overflowing_rem(ys).0 as u64)
        ^ (x16.saturating_div(y16) as u64).rotate_left(3)
}
#[no_mangle]
pub extern "C" fn minneg1_trap64(a: i64, b: i64) -> i64 {
    a / b + a % b
}
#[no_mangle]
pub extern "C" fn minneg1_trap8(a: i32, b: i32) -> i32 {
    ((a as i8) % (b as i8)) as i32
}
#[no_mangle]
pub extern "C" fn newer_apis(a: u32, b: u32) -> u64 {
    let d = if b == 0 { 1 } else { b };
    (a.div_ceil(d) as u64)
        ^ (a.checked_next_multiple_of(d).unwrap_or(7) as u64) << 32
        ^ (a.is_multiple_of(b) as u64) << 63
        ^ ((a as u8).div_ceil(d as u8 | 1) as u64) << 40
        ^ ((a as u64).div_ceil(d as u64)).rotate_left(3)
        ^ ((a as i32).cast_unsigned() as u64) << 1
        ^ (a.cast_signed().unsigned_abs() as u64) << 2
        ^ ((a as u16).next_multiple_of(d as u16 | 1) as u64) << 48
}
#[no_mangle]
pub extern "C" fn mixed_sign(a: i64, b: i64) -> u64 {
    let (x, y) = (a as u32, b as i32);
    x.checked_add_signed(y).map(|v| v as u64).unwrap_or(1 << 40)
        ^ (x.wrapping_add_signed(y) as u64).rotate_left(3)
        ^ ((a as i16)
            .checked_sub_unsigned(b as u16)
            .map(|v| v as u16 as u64)
            .unwrap_or(1 << 41))
        .rotate_left(7)
        ^ ((a as u64).saturating_add_signed(b)).rotate_left(11)
        ^ ((a as i8).wrapping_add_unsigned(b as u8) as u8 as u64) << 50
        ^ ((a as u128)
            .checked_add_signed((b as i128) << 70)
            .map(|v| (v >> 60) as u64)
            .unwrap_or(99))
        .rotate_left(13)
        ^ ((a as usize)
            .checked_sub(b as usize)
            .map(|v| v as u64)
            .unwrap_or(1 << 45))
}
#[no_mangle]
pub extern "C" fn isqrt_signed(a: i64) -> u64 {
    a.checked_isqrt().map(|v| v as u64).unwrap_or(1 << 50)
        ^ ((a as i32).checked_isqrt().map(|v| v as u64).unwrap_or(3)).rotate_left(20)
        ^ ((a as i8).checked_isqrt().map(|v| v as u64).unwrap_or(4)).rotate_left(40)
        ^ ((a as i128) * 1000)
            .checked_isqrt()
            .map(|v| v as u64)
            .unwrap_or(5)
}
#[no_mangle]
pub extern "C" fn ilog_base(a: i64, b: i64) -> u64 {
    let x = a as u64;
    let base = (b as u64) % 40;
    (x.checked_ilog(base).unwrap_or(99) as u64)
        ^ ((x as u8).checked_ilog(base as u8).unwrap_or(98) as u64) << 8
        ^ ((x as u128 * 1_000_000_000_000)
            .checked_ilog(base as u128)
            .unwrap_or(97) as u64)
            << 16
        ^ ((a as i16).checked_ilog(base as i16).unwrap_or(96) as u64) << 24
        ^ ((x as usize).checked_ilog10().unwrap_or(95) as u64) << 32
}
