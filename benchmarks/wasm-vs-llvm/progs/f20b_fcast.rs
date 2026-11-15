#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f20: float <-> int as-casts at every integer width (saturating semantics)
#[no_mangle]
pub extern "C" fn f32_to_u8(a: f32) -> u32 {
    (a as u8) as u32
}
#[no_mangle]
pub extern "C" fn f32_to_i8(a: f32) -> i32 {
    (a as i8) as i32
}
#[no_mangle]
pub extern "C" fn f64_to_u16(a: f64) -> u32 {
    (a as u16) as u32
}
#[no_mangle]
pub extern "C" fn f64_to_i16(a: f64) -> i32 {
    (a as i16) as i32
}
#[no_mangle]
pub extern "C" fn f64_to_words(a: f64) -> u64 {
    (a as u32 as u64)
        ^ (a as i32 as u32 as u64) << 32
        ^ (a as usize as u64).rotate_left(7)
        ^ (a as isize as i64 as u64).rotate_left(13)
}
#[no_mangle]
pub extern "C" fn f64_to_64(a: f64) -> u64 {
    (a as u64) ^ (a as i64 as u64).rotate_left(17)
}
#[no_mangle]
pub extern "C" fn f32_to_64(a: f32) -> u64 {
    (a as u64) ^ (a as i64 as u64).rotate_left(17) ^ (a as u32 as u64).rotate_left(3)
}
#[no_mangle]
pub extern "C" fn int_to_f(a: i64) -> u64 {
    (a as f32).to_bits() as u64
        ^ ((a as u64) as f32).to_bits() as u64 * 3
        ^ (a as f64).to_bits()
        ^ ((a as u64) as f64).to_bits().rotate_left(1)
        ^ ((a as i8) as f32).to_bits() as u64
        ^ ((a as u16) as f64).to_bits().rotate_left(2)
        ^ ((a as u32) as f32).to_bits() as u64 * 7
        ^ ((a as i32) as f64).to_bits().rotate_left(3)
        ^ ((a as usize) as f64).to_bits().rotate_left(4)
        ^ ((a as isize) as f32).to_bits() as u64 * 11
}
