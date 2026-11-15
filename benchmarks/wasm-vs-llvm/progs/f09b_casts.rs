#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f09: as-casts between every pair of integer widths
#[inline(always)]
fn h(x: u128) -> u64 {
    (x as u64) ^ ((x >> 64) as u64).rotate_left(29)
}
macro_rules! row {
    ($name:ident, $src:ty) => {
        #[inline(never)]
        fn $name(v: $src) -> u64 {
            let mut r = 0u64;
            r = r.rotate_left(5) ^ (v as i8 as i64 as u64);
            r = r.rotate_left(5) ^ (v as u8 as u64);
            r = r.rotate_left(5) ^ (v as i16 as i64 as u64);
            r = r.rotate_left(5) ^ (v as u16 as u64);
            r = r.rotate_left(5) ^ (v as i32 as i64 as u64);
            r = r.rotate_left(5) ^ (v as u32 as u64);
            r = r.rotate_left(5) ^ (v as i64 as u64);
            r = r.rotate_left(5) ^ (v as u64);
            r = r.rotate_left(5) ^ h(v as i128 as u128);
            r = r.rotate_left(5) ^ h(v as u128);
            r = r.rotate_left(5) ^ (v as isize as i64 as u64);
            r = r.rotate_left(5) ^ (v as usize as u64);
            r = r.rotate_left(5) ^ (v as isize as i128 as u128 >> 64) as u64;
            r = r.rotate_left(5) ^ (v as usize as i128 >> 1) as u64;
            r
        }
    };
}
row!(from_i8, i8);
row!(from_u8, u8);
row!(from_i16, i16);
row!(from_u16, u16);
row!(from_i32, i32);
row!(from_u32, u32);
row!(from_i64, i64);
row!(from_u64, u64);
row!(from_i128, i128);
row!(from_u128, u128);
row!(from_isize, isize);
row!(from_usize, usize);
#[no_mangle]
pub extern "C" fn cast_small(a: i32) -> u64 {
    from_i8(a as i8)
        ^ from_u8(a as u8).rotate_left(1)
        ^ from_i16(a as i16).rotate_left(2)
        ^ from_u16(a as u16).rotate_left(3)
}
#[no_mangle]
pub extern "C" fn cast_32(a: i32) -> u64 {
    from_i32(a)
        ^ from_u32(a as u32).rotate_left(1)
        ^ from_isize(a as isize).rotate_left(2)
        ^ from_usize(a as usize).rotate_left(3)
}
#[no_mangle]
pub extern "C" fn cast_64(a: i64) -> u64 {
    from_i64(a) ^ from_u64(a as u64).rotate_left(1)
}
#[no_mangle]
pub extern "C" fn cast_128(a: i64, b: i64) -> u64 {
    let x = ((a as i128) << 64) | (b as u64 as i128);
    from_i128(x)
        ^ from_u128(x as u128).rotate_left(1)
        ^ from_i128(b as i128).rotate_left(2)
        ^ from_u128((a as u128) << 1).rotate_left(3)
}
#[no_mangle]
pub extern "C" fn cast_i8_row(a: i32) -> u64 {
    from_i8(a as i8)
}
#[no_mangle]
pub extern "C" fn cast_isize_row(a: i32) -> u64 {
    from_isize(a as isize)
}
#[no_mangle]
pub extern "C" fn cast_usize_row(a: i32) -> u64 {
    from_usize(a as usize)
}
#[no_mangle]
pub extern "C" fn cast_i128_row(a: i64, b: i64) -> u64 {
    from_i128(((a as i128) << 64) | (b as u64 as i128))
}
#[no_mangle]
pub extern "C" fn cast_inline(a: i64) -> u64 {
    // direct chains, no helper
    let x = a as u8 as i8 as i32 as u16 as i64 as usize as i128 as isize as u64;
    let y = a as i32 as u128 as i16 as u64;
    let z = (a as usize as u128) << 100 >> 100;
    x ^ y.rotate_left(3) ^ h(z).rotate_left(5) ^ (a as isize as u128 >> 64) as u64
}
#[no_mangle]
pub extern "C" fn cast_bool_char(a: i32) -> u64 {
    let c = char::from_u32((a as u32) & 0x1fffff).unwrap_or('x');
    (c as u8 as u64)
        ^ (c as u32 as u64) << 8
        ^ ((a != 0) as u16 as u64) << 40
        ^ ((a < 0) as i64 as u64) << 41
        ^ ((a as u8) as char as u32 as u64) << 48
        ^ (true as i128 as u64) << 60
}
