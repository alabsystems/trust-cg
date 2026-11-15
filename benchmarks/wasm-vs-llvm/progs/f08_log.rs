#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f08: ilog2/ilog10/isqrt/midpoint/abs_diff/min/max/clamp
#[no_mangle]
pub extern "C" fn ilog_u32(a: u32, b: u32) -> u32 {
    a.ilog2() | a.ilog10() << 8 | (a.checked_ilog(b).unwrap_or(99)) << 16
}
#[no_mangle]
pub extern "C" fn ilog_small(a: i32, b: i32) -> u32 {
    let x = a as u8;
    let y = a as u16;
    let z = b as i16;
    x.checked_ilog2().unwrap_or(77)
        | y.checked_ilog10().unwrap_or(66) << 8
        | z.checked_ilog2().unwrap_or(55) << 16
        | (b as i8).checked_ilog10().unwrap_or(44) << 24
}
#[no_mangle]
pub extern "C" fn ilog_u64(a: u64, b: u64) -> u64 {
    (a.checked_ilog2().unwrap_or(200) as u64)
        | (a.checked_ilog10().unwrap_or(201) as u64) << 8
        | (a.checked_ilog(b).unwrap_or(202) as u64) << 16
        | ((a as i64).checked_ilog10().unwrap_or(203) as u64) << 24
}
#[no_mangle]
pub extern "C" fn ilog_u128(a: u64, b: u64) -> u64 {
    let x = ((a as u128) << 64) | b as u128;
    (x.checked_ilog2().unwrap_or(200) as u64)
        | (x.checked_ilog10().unwrap_or(201) as u64) << 8
        | ((b as u128).checked_ilog10().unwrap_or(203) as u64) << 24
}
#[no_mangle]
pub extern "C" fn isqrt_all(a: u64, b: u64) -> u64 {
    let x = ((a as u128) << 64) | b as u128;
    (a.isqrt())
        ^ ((a as u32).isqrt() as u64) << 7
        ^ ((a as u16).isqrt() as u64) << 40
        ^ ((a as u8).isqrt() as u64) << 58
        ^ (x.isqrt() as u64).rotate_left(3)
        ^ (b as i64).checked_isqrt().unwrap_or(5) as u64
}
#[no_mangle]
pub extern "C" fn midpoint_u(a: u64, b: u64) -> u64 {
    a.midpoint(b)
        ^ ((a as u32).midpoint(b as u32) as u64) << 1
        ^ ((a as u8).midpoint(b as u8) as u64) << 40
        ^ ((a as u16).midpoint(b as u16) as u64) << 48
        ^ ((a as usize).midpoint(b as usize) as u64) << 5
}
#[no_mangle]
pub extern "C" fn midpoint_s(a: i64, b: i64) -> u64 {
    (a.midpoint(b) as u64)
        ^ ((a as i32).midpoint(b as i32) as u32 as u64) << 1
        ^ ((a as i8).midpoint(b as i8) as u8 as u64) << 40
        ^ ((a as i16).midpoint(b as i16) as u16 as u64) << 48
}
#[no_mangle]
pub extern "C" fn absdiff_all(a: i64, b: i64) -> u64 {
    a.abs_diff(b)
        ^ (a as u64).abs_diff(b as u64).rotate_left(7)
        ^ ((a as i32).abs_diff(b as i32) as u64) << 3
        ^ ((a as i8).abs_diff(b as i8) as u64) << 50
        ^ ((a as u16).abs_diff(b as u16) as u64) << 30
        ^ ((a as isize).abs_diff(b as isize) as u64) << 1
}
#[no_mangle]
pub extern "C" fn minmax_all(a: i64, b: i64) -> u64 {
    (a.min(b) ^ a.max(b).rotate_left(1)) as u64
        ^ ((a as u64).min(b as u64)) << 2
        ^ ((a as i8).max(b as i8) as u8 as u64) << 56
        ^ ((a as u16).min(b as u16) as u64) << 40
        ^ ((a as i32).max(b as i32) as u32 as u64) << 9
        ^ (((a as i128) << 64).min((b as i128) << 60) >> 60) as u64
}
#[no_mangle]
pub extern "C" fn clamp_all(a: i32, b: i32) -> u64 {
    let lo = b.min(b.wrapping_add(100));
    let hi = b.max(b.wrapping_add(100));
    (a.clamp(lo, hi) as u32 as u64)
        ^ ((a as u8).clamp(3, 200) as u64) << 32
        ^ ((a as i16).clamp(-5, 300) as u16 as u64) << 40
        ^ ((a as i64).clamp(-(1 << 40), 1 << 33) as u64).rotate_left(5)
}
