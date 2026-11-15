#![no_std]
#![allow(dead_code, arithmetic_overflow, unconditional_panic)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[no_mangle]
pub extern "C" fn ck_usize_add(a: u32, b: u32) -> u64 {
    let x = a as usize;
    let y = b as usize;
    (x + y) as u64
}

#[no_mangle]
pub extern "C" fn ck_usize_mul(a: u32, b: u32) -> u64 {
    let x = a as usize;
    let y = b as usize;
    (x * y) as u64
}

#[no_mangle]
pub extern "C" fn ck_usize_sub(a: u32, b: u32) -> u64 {
    let x = a as usize;
    let y = b as usize;
    (x - y) as u64
}

#[no_mangle]
pub extern "C" fn ck_isize_add(a: i32, b: i32) -> i64 {
    let x = a as isize;
    let y = b as isize;
    (x + y) as i64
}

#[no_mangle]
pub extern "C" fn ck_isize_mul(a: i32, b: i32) -> i64 {
    let x = a as isize;
    let y = b as isize;
    (x * y) as i64
}

#[no_mangle]
pub extern "C" fn ck_isize_neg(a: i32, b: i32) -> i64 {
    let x = a as isize;
    (-x) as i64 ^ b as i64
}

#[no_mangle]
pub extern "C" fn ck_isize_div(a: i32, b: i32) -> i64 {
    let x = a as isize;
    let y = b as isize;
    (x / y) as i64
}

#[no_mangle]
pub extern "C" fn ck_usize_shl(a: u32, b: u32) -> u64 {
    let x = a as usize;
    (x << (b % 40)) as u64
}

#[no_mangle]
pub extern "C" fn ck_isize_abs(a: i32, b: i32) -> i64 {
    let x = (a as isize).wrapping_add(b as isize);
    x.abs() as i64
}

#[no_mangle]
pub extern "C" fn ck_usize_pow(a: u32, b: u32) -> u64 {
    (a as usize).pow(b % 6) as u64
}
