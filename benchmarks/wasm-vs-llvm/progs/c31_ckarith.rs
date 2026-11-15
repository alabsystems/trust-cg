#![no_std]
#![allow(dead_code)]
#![feature(core_float_math, float_minimum_maximum)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
#[no_mangle]
pub extern "C" fn ck_u8add(x: f32) -> u32 {
    ((x as u8) + 200) as u32
}
#[no_mangle]
pub extern "C" fn ck_i8abs(x: f64) -> i32 {
    (x as i8).abs() as i32
}
#[no_mangle]
pub extern "C" fn ck_shl(x: f32, y: f32) -> u32 {
    (x as u32) << (y as u32)
}
#[no_mangle]
pub extern "C" fn ck_div(x: f64, y: f64) -> i32 {
    (x as i32) / (y as i32)
}
#[no_mangle]
pub extern "C" fn ck_rem64(x: f64, y: f64) -> i64 {
    (x as i64) % (y as i64)
}
#[no_mangle]
pub extern "C" fn ck_mul16(x: f32, y: f32) -> i32 {
    ((x as i16) * (y as i16)) as i32
}
#[no_mangle]
pub extern "C" fn ck_neg(x: f64) -> i64 {
    -(x as i64)
}
#[no_mangle]
pub extern "C" fn ck_sub_u64(x: f64, y: f32) -> u64 {
    (x as u64) - (y as u64)
}
#[no_mangle]
pub extern "C" fn ck_usize(x: f64, y: f64) -> u32 {
    ((x as usize) + (y as usize)) as u32
}
#[no_mangle]
pub extern "C" fn ck_idx(x: f32) -> u32 {
    let t = [1u32, 2, 3, 4, 5];
    t[x as usize]
}
