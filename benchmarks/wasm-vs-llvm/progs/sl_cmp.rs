#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
static A8: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
static B8: [u8; 8] = [1, 2, 3, 9, 5, 6, 7, 8];
static A64: [u64; 5] = [1, u64::MAX, 3, 1 << 63, 5];
static B64: [u64; 5] = [1, u64::MAX, 3, 1 << 62, 5];
static AI: [i32; 5] = [-1, 5, i32::MIN, 7, 0];
static BI: [i32; 5] = [-1, 5, i32::MAX, 7, 0];

#[inline(never)]
fn eq8(a: &[u8], b: &[u8]) -> bool {
    a == b
}
#[inline(never)]
fn cmp8(a: &[u8], b: &[u8]) -> i32 {
    match a.cmp(b) {
        core::cmp::Ordering::Less => -1,
        core::cmp::Ordering::Equal => 0,
        core::cmp::Ordering::Greater => 1,
    }
}
#[no_mangle]
pub extern "C" fn e_eq8(a: u32, b: u32) -> u32 {
    let x = &A8[(a % 9) as usize..];
    let y = &B8[(b % 9) as usize..];
    eq8(x, y) as u32 | (eq8(x, &A8[(b % 9) as usize..]) as u32) << 1
}
#[no_mangle]
pub extern "C" fn e_cmp8(a: u32, b: u32) -> i32 {
    let x = &A8[..(a % 9) as usize];
    let y = &B8[..(b % 9) as usize];
    cmp8(x, y) * 10 + cmp8(y, x)
}
#[inline(never)]
fn eq64(a: &[u64], b: &[u64]) -> bool {
    a == b
}
#[no_mangle]
pub extern "C" fn e_eq64(a: u32, b: u32) -> u32 {
    let x = &A64[..(a % 6) as usize];
    let y = &B64[..(b % 6) as usize];
    eq64(x, y) as u32 | (eq64(x, &A64[..(b % 6) as usize]) as u32) << 1
}
#[inline(never)]
fn cmp64(a: &[u64], b: &[u64]) -> i32 {
    match a.cmp(b) {
        core::cmp::Ordering::Less => -1,
        core::cmp::Ordering::Equal => 0,
        core::cmp::Ordering::Greater => 1,
    }
}
#[no_mangle]
pub extern "C" fn e_cmp64(a: u32, b: u32) -> i32 {
    let x = &A64[..(a % 6) as usize];
    let y = &B64[..(b % 6) as usize];
    cmp64(x, y) * 10 + cmp64(y, x)
}
#[inline(never)]
fn cmpi(a: &[i32], b: &[i32]) -> i32 {
    match a.cmp(b) {
        core::cmp::Ordering::Less => -1,
        core::cmp::Ordering::Equal => 0,
        core::cmp::Ordering::Greater => 1,
    }
}
#[no_mangle]
pub extern "C" fn e_cmpi(a: u32, b: u32) -> i32 {
    let x = &AI[..(a % 6) as usize];
    let y = &BI[..(b % 6) as usize];
    cmpi(x, y) * 10 + cmpi(y, x)
}
#[no_mangle]
pub extern "C" fn e_str_cmp(a: u32, b: u32) -> i32 {
    let s = "abcdefgh";
    let t = "abcxefgh";
    let x = &s[..(a % 9) as usize];
    let y = &t[..(b % 9) as usize];
    match x.cmp(y) {
        core::cmp::Ordering::Less => -1,
        core::cmp::Ordering::Equal => 0,
        core::cmp::Ordering::Greater => 1,
    }
}
#[no_mangle]
pub extern "C" fn e_arr_eq(a: u32) -> u32 {
    let x = [a, a ^ 1, 7];
    let y = [a, a ^ 1, a % 9];
    (x == y) as u32
}
#[no_mangle]
pub extern "C" fn e_partial_cmp_f64(a: u32, b: u32) -> i32 {
    let fa = [1.0f64, f64::NAN, -0.0, 2.0];
    let fb = [1.0f64, 3.0, 0.0, 2.0];
    let x = &fa[..(a % 5) as usize];
    let y = &fb[..(b % 5) as usize];
    match x.partial_cmp(y) {
        Some(core::cmp::Ordering::Less) => -1,
        Some(core::cmp::Ordering::Equal) => 0,
        Some(core::cmp::Ordering::Greater) => 1,
        None => 9,
    }
}
