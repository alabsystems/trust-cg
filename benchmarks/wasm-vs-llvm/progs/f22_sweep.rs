#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f22: randomized sweeps (splitmix) over every width; each export = 64 random operand pairs folded into a hash
#[inline(always)]
fn sm(s: &mut u64) -> u64 {
    *s = s.wrapping_add(0x9e3779b97f4a7c15);
    let mut z = *s;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}
#[inline(always)]
fn shape(r: u64, k: u64) -> u64 {
    match k % 4 {
        0 => r,
        1 => r >> (r % 64),
        2 => !(r >> (r % 64)),
        _ => r & 0x8000_0000_0000_00ff,
    }
}
#[inline(always)]
fn h(x: u128) -> u64 {
    (x as u64) ^ ((x >> 64) as u64).rotate_left(29)
}
macro_rules! sweep {
    ($name:ident, $t:ty, $ut:ty) => {
        #[no_mangle]
        pub extern "C" fn $name(seed: i64) -> u64 {
            let mut s = seed as u64;
            let mut acc = 0u64;
            let mut i = 0u64;
            while i < 64 {
                let r1 = sm(&mut s);
                let r2 = sm(&mut s);
                let r3 = sm(&mut s);
                let x = (shape(r1, r3) as u128 | (shape(r2, r3 >> 2) as u128) << 64) as $t;
                let y =
                    (shape(r2, r3 >> 4) as u128 | (shape(r1 ^ r3, r3 >> 6) as u128) << 64) as $t;
                let n = (r3 >> 8) as u32;
                let v: [u64; 16] = [
                    h(x.wrapping_add(y) as u128),
                    h(x.wrapping_sub(y) as u128),
                    h(x.wrapping_mul(y) as u128),
                    match x.checked_div(y) {
                        Some(q) => h(q as u128),
                        None => 1,
                    },
                    match x.checked_rem(y) {
                        Some(q) => h(q as u128),
                        None => 2,
                    },
                    h(x.wrapping_shl(n) as u128),
                    h(x.wrapping_shr(n) as u128),
                    h(x.rotate_left(n) as u128),
                    h(x.saturating_add(y) as u128),
                    h(x.saturating_sub(y) as u128),
                    (x.count_ones() as u64)
                        | (x.leading_zeros() as u64) << 8
                        | (x.trailing_zeros() as u64) << 16,
                    ((x < y) as u64) | ((x == y) as u64) << 1 | ((x >= y) as u64) << 2,
                    h(x.abs_diff(y) as u128),
                    h(x.max(y) as u128) ^ h(x.min(y) as u128),
                    h(x.swap_bytes() as u128) ^ h(x.reverse_bits() as u128),
                    h((x as $ut) as u128) ^ h(((x as i128) >> 3) as u128),
                ];
                let mut j = 0;
                while j < 16 {
                    acc = acc.rotate_left(7) ^ v[j];
                    j += 1;
                }
                i += 1;
            }
            acc
        }
    };
}
sweep!(sw_u8, u8, i8);
sweep!(sw_i8, i8, u8);
sweep!(sw_u16, u16, i16);
sweep!(sw_i16, i16, u16);
sweep!(sw_u32, u32, i32);
sweep!(sw_i32, i32, u32);
sweep!(sw_u64, u64, i64);
sweep!(sw_i64, i64, u64);
sweep!(sw_usize, usize, isize);
sweep!(sw_isize, isize, usize);
