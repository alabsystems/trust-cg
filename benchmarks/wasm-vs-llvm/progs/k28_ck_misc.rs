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
pub extern "C" fn ck_u8_shl(a: u32, b: u32) -> u32 {
    ((a as u8) << (b % 12)) as u32
}

#[no_mangle]
pub extern "C" fn ck_i16_shr(a: i32, b: u32) -> i32 {
    ((a as i16) >> (b % 20)) as i32
}

#[no_mangle]
pub extern "C" fn ck_i128_add(a: i64, b: i64) -> i64 {
    let x = (a as i128) << 63;
    let y = (b as i128) << 64;
    (x + y + y) as i64
}

#[no_mangle]
pub extern "C" fn ck_i128_mul(a: i64, b: i64) -> i64 {
    let x = (a as i128) << 40;
    let y = (b as i128) << 40;
    ((x * y) >> 64) as i64
}

#[no_mangle]
pub extern "C" fn ck_u128_sub(a: u64, b: u64) -> u64 {
    let x = (a as u128) << 64;
    let y = ((b as u128) << 64) | 5;
    ((x - y) >> 3) as u64
}

#[no_mangle]
pub extern "C" fn ck_i64_mul(a: i64, b: i64) -> i64 {
    a * b
}

#[no_mangle]
pub extern "C" fn ck_u64_add(a: u64, b: u64) -> u64 {
    a + b
}

#[no_mangle]
pub extern "C" fn ck_i32_rem(a: i32, b: i32) -> i32 {
    a % b
}

#[no_mangle]
pub extern "C" fn ck_i64_div(a: i64, b: i64) -> i64 {
    a / b
}

#[no_mangle]
pub extern "C" fn ck_u32_pow(a: u32, b: u32) -> u32 {
    a.pow(b % 9)
}
