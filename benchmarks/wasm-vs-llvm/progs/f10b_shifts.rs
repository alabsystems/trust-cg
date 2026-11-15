#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f10: shifts
#[inline(always)]
fn h(x: u128) -> u64 {
    (x as u64) ^ ((x >> 64) as u64).rotate_left(29)
}
#[no_mangle]
pub extern "C" fn shl_u8_trap(a: i32, b: i32) -> u32 {
    ((a as u8) << (b as u32)) as u32
}
#[no_mangle]
pub extern "C" fn shr_i8_trap(a: i32, b: i32) -> i32 {
    ((a as i8) >> (b as u32)) as i32
}
#[no_mangle]
pub extern "C" fn shr_i16_by_i16(a: i32, b: i32) -> i32 {
    ((a as i16) >> (b as i16)) as i32 ^ ((a as u16) << (b as i8)) as i32
}
#[no_mangle]
pub extern "C" fn shl_i32_trap(a: i32, b: i32) -> i32 {
    a << b
}
#[no_mangle]
pub extern "C" fn shr_u64_trap(a: u64, b: u64) -> u64 {
    a >> b ^ ((a as i64) >> (b as u8)) as u64
}
#[no_mangle]
pub extern "C" fn shift_u128(a: u64, b: u32) -> u64 {
    let x = ((a as u128) << 64) | (!a as u128);
    let n = b % 128;
    h(x << n) ^ h(x >> n).rotate_left(1) ^ h(((x as i128) >> n) as u128).rotate_left(2)
}
#[no_mangle]
pub extern "C" fn shift_u128_trap(a: u64, b: u32) -> u64 {
    let x = ((a as u128) << 64) | (a as u128);
    h(x << b) ^ h(((x as i128) >> b) as u128)
}
#[no_mangle]
pub extern "C" fn wshift_all(a: i64, b: i64) -> u64 {
    let n = b as u32;
    (a.wrapping_shl(n) as u64)
        ^ ((a as u8).wrapping_shr(n) as u64) << 1
        ^ ((a as i16).wrapping_shr(n) as u64) << 3
        ^ ((a as i32).wrapping_shl(n) as u32 as u64) << 5
        ^ ((a as usize).wrapping_shr(n) as u64) << 7
        ^ h(((a as i128) << 70).wrapping_shr(n) as u128)
        ^ h((a as u128).wrapping_shl(n)).rotate_left(11)
}
#[inline(never)]
fn e(o: Option<u64>) -> u64 {
    match o {
        Some(v) => v.rotate_left(3) | 1,
        None => 0,
    }
}
#[no_mangle]
pub extern "C" fn cshift_all(a: i64, b: i64) -> u64 {
    let n = b as u32;
    e(a.checked_shl(n).map(|v| v as u64))
        ^ e((a as u8).checked_shr(n).map(|v| v as u64)).rotate_left(5)
        ^ e((a as i16).checked_shr(n).map(|v| v as u64)).rotate_left(9)
        ^ e((a as u32).checked_shl(n).map(|v| v as u64)).rotate_left(13)
        ^ e((a as isize).checked_shl(n).map(|v| v as u64)).rotate_left(17)
        ^ match (a as u128).checked_shl(n) {
            Some(v) => h(v).rotate_left(21),
            None => 0,
        }
        ^ match ((a as i128) << 64).checked_shr(n) {
            Some(v) => h(v as u128).rotate_left(25),
            None => 0,
        }
}
#[no_mangle]
pub extern "C" fn unbounded(a: i64, b: i64) -> u64 {
    let n = b as u32;
    a.unbounded_shl(n) as u64
        ^ (a.unbounded_shr(n) as u64).rotate_left(7)
        ^ ((a as u8).unbounded_shl(n) as u64) << 50
        ^ ((a as i32).unbounded_shr(n) as u32 as u64) << 11
        ^ h((a as u128).unbounded_shl(n)).rotate_left(3)
}
