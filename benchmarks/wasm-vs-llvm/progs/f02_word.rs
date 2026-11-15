#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f02: 32/64-bit and usize/isize + - * / % with overflow checks
#[no_mangle]
pub extern "C" fn i32_add(a: i32, b: i32) -> i32 {
    a + b
}
#[no_mangle]
pub extern "C" fn i32_div(a: i32, b: i32) -> i32 {
    a / b
}
#[no_mangle]
pub extern "C" fn i32_rem(a: i32, b: i32) -> i32 {
    a % b
}
#[no_mangle]
pub extern "C" fn u32_mul(a: u32, b: u32) -> u32 {
    a * b
}
#[no_mangle]
pub extern "C" fn i64_mul(a: i64, b: i64) -> i64 {
    a * b
}
#[no_mangle]
pub extern "C" fn i64_divrem(a: i64, b: i64) -> i64 {
    (a / b) ^ (a % b).rotate_left(17)
}
#[no_mangle]
pub extern "C" fn u64_sub(a: u64, b: u64) -> u64 {
    a - b
}
#[no_mangle]
pub extern "C" fn usize_ops(a: u32, b: u32) -> u32 {
    let (x, y) = (a as usize, b as usize);
    let s = x.wrapping_add(y);
    let m = x.checked_mul(y).unwrap_or(usize::MAX);
    let d = if y != 0 { x / y + x % y } else { 7 };
    (s ^ m.rotate_left(5) ^ d) as u32 ^ (core::mem::size_of::<usize>() as u32)
}
#[no_mangle]
pub extern "C" fn isize_ops(a: i32, b: i32) -> i32 {
    let (x, y) = (a as isize, b as isize);
    let s = x.wrapping_sub(y);
    let m = x.checked_mul(y).unwrap_or(isize::MIN);
    let d = x.checked_div(y).unwrap_or(3) ^ x.checked_rem(y).unwrap_or(5);
    (s ^ m ^ d ^ (isize::MAX >> 3)) as i32
}
#[no_mangle]
pub extern "C" fn isize_add_trap(a: i32, b: i32) -> i32 {
    (a as isize + b as isize) as i32
}
