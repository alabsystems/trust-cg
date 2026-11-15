#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f27: usize arithmetic mixed with slice lengths, size_of/align_of, and index math
static D: [u16; 37] = [3; 37];
#[inline(never)]
fn len_of(s: &[u16]) -> usize {
    s.len()
}
#[no_mangle]
pub extern "C" fn len_math(a: u32, b: u32) -> u64 {
    let lo = (a % 38) as usize;
    let hi = (b % 38) as usize;
    if lo > hi {
        return 7;
    }
    let s = &D[lo..hi];
    let n = len_of(s);
    let bytes = n * core::mem::size_of::<u16>();
    let big = n
        .checked_mul(usize::MAX / 3)
        .map(|v| v as u64)
        .unwrap_or(1 << 40);
    let neg = (n as isize).wrapping_neg() as usize;
    let sh = n.wrapping_shl(a) ^ n.rotate_right(b);
    (bytes as u64)
        ^ big.rotate_left(3)
        ^ (neg as u64).rotate_left(9)
        ^ (sh as u64).rotate_left(17)
        ^ ((n as u64) << 50)
        ^ (core::mem::size_of::<usize>() as u64 * 1000
            + core::mem::align_of::<u64>() as u64 * 100
            + core::mem::align_of::<u128>() as u64)
            << 20
}
#[no_mangle]
pub extern "C" fn idx_math(a: u32, b: u32) -> u32 {
    let i = (a as usize).wrapping_mul(2654435761) % 37;
    let j = (b as usize) >> 3;
    let k = i.saturating_sub(j) + (i ^ j).min(36) / 2;
    D[k.min(36)] as u32 + k as u32 * 1000 + (usize::BITS - k.leading_zeros()) * 100000
}
#[no_mangle]
pub extern "C" fn isize_math(a: i32, b: i32) -> i64 {
    let x = a as isize;
    let y = b as isize;
    let m = x.checked_mul(y).unwrap_or(isize::MAX);
    let d = x.checked_div(y).unwrap_or(isize::MIN);
    let r = x.rem_euclid(if y == 0 { 1 } else { y }.wrapping_abs().max(1));
    (m as i64)
        ^ (d as i64).rotate_left(20)
        ^ (r as i64).rotate_left(40)
        ^ ((x.signum() + y.signum()) as i64) << 60
        ^ ((x as i64) - (y as i64)).wrapping_mul(isize::MAX as i64)
        ^ ((x.abs_diff(y)) as u64 as i64) << 2
}
#[no_mangle]
pub extern "C" fn usize_u64_mix(a: i64, b: i64) -> u64 {
    let x = a as usize;
    let y = b as u64;
    let z = (x as u64).wrapping_mul(y)
        ^ ((y as usize).wrapping_mul(x) as u64)
        ^ ((x as u128 * y as u128) >> 32) as u64;
    z ^ ((x as i64).wrapping_add(b) as u64)
        ^ ((usize::MAX as u64) + 1)
        ^ ((x.count_ones() + y.count_ones()) as u64) << 58
}
