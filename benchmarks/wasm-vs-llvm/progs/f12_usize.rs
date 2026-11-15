#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f12: usize/isize overflow checks must fire at 32 bits on wasm32
#[no_mangle]
pub extern "C" fn us_add(a: u32, b: u32) -> u32 {
    ((a as usize) + (b as usize)) as u32
}
#[no_mangle]
pub extern "C" fn us_sub(a: u32, b: u32) -> u32 {
    ((a as usize) - (b as usize)) as u32
}
#[no_mangle]
pub extern "C" fn us_mul(a: u32, b: u32) -> u32 {
    ((a as usize) * (b as usize)) as u32
}
#[no_mangle]
pub extern "C" fn us_shl(a: u32, b: u32) -> u32 {
    ((a as usize) << b) as u32 ^ ((a as usize) >> (b as usize)) as u32
}
#[no_mangle]
pub extern "C" fn is_neg(a: i32) -> i32 {
    (-(a as isize)) as i32
}
#[no_mangle]
pub extern "C" fn is_divrem(a: i32, b: i32) -> i32 {
    ((a as isize) / (b as isize)) as i32 ^ ((a as isize) % (b as isize)) as i32
}
#[no_mangle]
pub extern "C" fn is_mul(a: i32, b: i32) -> i32 {
    ((a as isize) * (b as isize)) as i32
}
#[no_mangle]
pub extern "C" fn is_shr(a: i32, b: i32) -> i32 {
    ((a as isize) >> b) as i32 ^ ((a as isize) << (b as i8)) as i32
}
#[no_mangle]
pub extern "C" fn us_from64(a: i64, b: i64) -> u64 {
    // lossless try_from / truncating as between u64 and usize on 32-bit
    let t = usize::try_from(a as u64)
        .map(|v| v as u64)
        .unwrap_or(0xdead);
    let u = isize::try_from(b)
        .map(|v| v as i64 as u64)
        .unwrap_or(0xbeef);
    let w = (a as usize) as u64 ^ ((b as isize) as i64 as u64).rotate_left(9);
    t ^ u.rotate_left(17)
        ^ w.rotate_left(33)
        ^ (usize::MAX as u64)
        ^ (isize::MIN as i64 as u64)
        ^ (usize::BITS as u64) << 60
}
#[no_mangle]
pub extern "C" fn us_float(a: f64) -> u64 {
    (a as usize) as u64
        ^ ((a as isize) as i64 as u64).rotate_left(32)
        ^ (((a as usize) as f64) as u64).rotate_left(7)
        ^ ((a as isize) as f32 as i64 as u64).rotate_left(13)
        ^ ((a as u32) as usize as f32).to_bits() as u64
}
