#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f07: bit ops across widths
#[inline(always)]
fn h(x: u128) -> u64 {
    (x as u64) ^ ((x >> 64) as u64).rotate_left(29)
}
#[no_mangle]
pub extern "C" fn bits_u8(a: i32, b: i32) -> u64 {
    let x = a as u8;
    let n = b as u32;
    (x.leading_zeros() as u64)
        | (x.trailing_zeros() as u64) << 4
        | (x.count_ones() as u64) << 8
        | (x.count_zeros() as u64) << 12
        | (x.rotate_left(n) as u64) << 16
        | (x.rotate_right(n) as u64) << 24
        | (x.reverse_bits() as u64) << 32
        | (x.leading_ones() as u64) << 40
        | (x.trailing_ones() as u64) << 44
        | ((x as i8).rotate_left(n) as u8 as u64) << 48
}
#[no_mangle]
pub extern "C" fn bits_i16(a: i32, b: i32) -> u64 {
    let x = a as i16;
    let n = b as u32;
    (x.leading_zeros() as u64)
        | (x.trailing_zeros() as u64) << 5
        | (x.count_ones() as u64) << 10
        | (x.rotate_left(n) as u16 as u64) << 16
        | (x.swap_bytes() as u16 as u64) << 32
        | (x.reverse_bits() as u16 as u64) << 48
            ^ (x.to_be() as u16 as u64)
            ^ (i16::from_le(x) as u16 as u64) << 7
            ^ (x.leading_ones() as u64) << 59
}
#[no_mangle]
pub extern "C" fn bits_u32(a: u32, b: u32) -> u64 {
    (a.leading_zeros() as u64)
        | (a.trailing_zeros() as u64) << 6
        | (a.count_ones() as u64) << 12
        | (a.rotate_right(b) as u64) << 18
            ^ (a.reverse_bits() as u64) << 5
            ^ (a.swap_bytes() as u64) << 31
            ^ (u32::from_be(a) as u64) << 1
            ^ (a.to_le() as u64) << 3
}
#[no_mangle]
pub extern "C" fn bits_i64(a: i64, b: i64) -> u64 {
    let n = b as u32;
    (a.leading_zeros() as u64)
        ^ (a.trailing_zeros() as u64) << 7
        ^ (a.count_ones() as u64) << 14
        ^ a.rotate_left(n) as u64
        ^ (a.reverse_bits() as u64).rotate_left(3)
        ^ (a.swap_bytes() as u64).rotate_left(9)
        ^ (a.to_be() as u64).rotate_left(17)
        ^ (a.leading_ones() as u64) << 50
        ^ (a.trailing_ones() as u64) << 57
}
#[no_mangle]
pub extern "C" fn bits_u128(a: u64, b: u64) -> u64 {
    let x = ((a as u128) << 64) | (b as u128);
    let n = b as u32;
    (x.leading_zeros() as u64)
        ^ (x.trailing_zeros() as u64) << 8
        ^ (x.count_ones() as u64) << 16
        ^ h(x.rotate_left(n))
        ^ h(x.rotate_right(n ^ 5)).rotate_left(7)
        ^ h(x.reverse_bits()).rotate_left(13)
        ^ h(x.swap_bytes()).rotate_left(19)
        ^ h(x.to_be()).rotate_left(23)
        ^ (x.leading_ones() as u64) << 40
}
#[no_mangle]
pub extern "C" fn bits_i128(a: i64, b: i64) -> u64 {
    let x = (a as i128) << 40 ^ (b as i128);
    (x.leading_zeros() as u64)
        ^ (x.trailing_zeros() as u64) << 8
        ^ (x.count_ones() as u64) << 16
        ^ h(x.rotate_left(b as u32) as u128)
        ^ h(x.reverse_bits() as u128).rotate_left(13)
        ^ h(i128::from_be(x) as u128).rotate_left(19)
        ^ (x.trailing_ones() as u64) << 40
}
#[no_mangle]
pub extern "C" fn bits_usize(a: u32, b: u32) -> u64 {
    let x = a as usize;
    (x.leading_zeros() as u64)
        | (x.trailing_zeros() as u64) << 6
        | (x.count_ones() as u64) << 12
        | (x.rotate_left(b) as u64) << 18
            ^ (x.reverse_bits() as u64) << 5
            ^ (x.swap_bytes() as u64) << 31
            ^ (x.is_power_of_two() as u64) << 63
            ^ (x.next_power_of_two() as u64) << 2
}
#[no_mangle]
pub extern "C" fn bits_isize(a: i32, b: i32) -> u64 {
    let x = a as isize;
    (x.leading_zeros() as u64)
        | (x.trailing_zeros() as u64) << 6
        | (x.count_ones() as u64) << 12
        | (x.rotate_right(b as u32) as usize as u64) << 18
            ^ (x.swap_bytes() as usize as u64) << 31
            ^ (x.leading_ones() as u64) << 58
}
#[no_mangle]
pub extern "C" fn npow2_trap(a: u32, b: u32) -> u64 {
    // next_power_of_two overflows in debug for > 2^31 -> panic
    (a.next_power_of_two() as u64) ^ ((b as u16).next_power_of_two() as u64) << 32
}
#[no_mangle]
pub extern "C" fn bytes_rt(a: u64, b: u64) -> u64 {
    let x = ((a as u128) << 64) | b as u128;
    let bl = x.to_le_bytes();
    let bb = x.to_be_bytes();
    let y = u128::from_le_bytes(bb);
    let z = u32::from_be_bytes([bl[0], bl[5], bl[10], bl[15]]);
    h(y) ^ z as u64 ^ (u16::from_ne_bytes([bb[3], bl[7]]) as u64) << 40
}
