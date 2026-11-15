#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f14: table-driven u128/i128 edge values; each export = one op over one (i, j) pair from the table
const T: [u128; 24] = [
    0,
    1,
    2,
    3,
    0xffff_ffff,
    1 << 32,
    (1 << 63) - 1,
    1 << 63,
    u64::MAX as u128,
    1 << 64,
    (1 << 64) + 1,
    (1 << 65) - 1,
    1 << 96,
    (1 << 127) - 1,
    1 << 127,
    u128::MAX,
    0x1234_5678_9abc_def0_0fed_cba9_8765_4321,
    10_000_000_000_000_000_000,
    100_000_000_000_000_000_000_000_000_000_000_000_000,
    3 * (1 << 64) - 7,
    u128::MAX - 1,
    (1 << 64) - 3,
    0xffff_ffff_0000_0000,
    7 << 61,
];
#[inline(always)]
fn h(x: u128) -> u64 {
    (x as u64) ^ ((x >> 64) as u64).rotate_left(29)
}
#[inline(never)]
fn pick(i: u32) -> u128 {
    T[(i % 24) as usize]
}
#[no_mangle]
pub extern "C" fn t_udiv(i: u32, j: u32) -> u64 {
    let (x, y) = (pick(i), pick(j));
    if y == 0 {
        return 1;
    }
    h(x / y) ^ h(x % y).rotate_left(1)
}
#[no_mangle]
pub extern "C" fn t_sdiv(i: u32, j: u32) -> u64 {
    let (x, y) = (pick(i) as i128, pick(j) as i128);
    match (x.checked_div(y), x.checked_rem(y)) {
        (Some(q), Some(r)) => h(q as u128) ^ h(r as u128).rotate_left(1),
        _ => 3,
    }
}
#[no_mangle]
pub extern "C" fn t_mul(i: u32, j: u32) -> u64 {
    let (x, y) = (pick(i), pick(j));
    h(x.wrapping_mul(y))
        ^ match x.checked_mul(y) {
            Some(v) => h(v).rotate_left(2),
            None => 5,
        }
        ^ match (x as i128).checked_mul(y as i128) {
            Some(v) => h(v as u128).rotate_left(3),
            None => 7,
        }
}
#[no_mangle]
pub extern "C" fn t_addsub(i: u32, j: u32) -> u64 {
    let (x, y) = (pick(i), pick(j));
    h(x.wrapping_add(y))
        ^ h(x.wrapping_sub(y)).rotate_left(1)
        ^ match x.checked_add(y) {
            Some(v) => h(v).rotate_left(2),
            None => 5,
        }
        ^ match (x as i128).checked_sub(y as i128) {
            Some(v) => h(v as u128).rotate_left(3),
            None => 7,
        }
        ^ match (x as i128).checked_add(y as i128) {
            Some(v) => h(v as u128).rotate_left(4),
            None => 9,
        }
}
#[no_mangle]
pub extern "C" fn t_cmp(i: u32, j: u32) -> u32 {
    let (x, y) = (pick(i), pick(j));
    let (p, q) = (x as i128, y as i128);
    (x < y) as u32
        | ((x <= y) as u32) << 1
        | ((x == y) as u32) << 2
        | ((p < q) as u32) << 3
        | ((p >= q) as u32) << 4
        | ((x.cmp(&y) as i8 as u8 as u32) << 8)
        | ((p.cmp(&q) as i8 as u8 as u32) << 16)
        | ((x.max(y) == x) as u32) << 24
        | ((p.min(q) == q) as u32) << 25
}
#[no_mangle]
pub extern "C" fn t_sat(i: u32, j: u32) -> u64 {
    let (x, y) = (pick(i), pick(j));
    let (p, q) = (x as i128, y as i128);
    h(x.saturating_add(y))
        ^ h(x.saturating_sub(y)).rotate_left(1)
        ^ h(x.saturating_mul(y)).rotate_left(2)
        ^ h(p.saturating_add(q) as u128).rotate_left(3)
        ^ h(p.saturating_sub(q) as u128).rotate_left(4)
        ^ h(p.saturating_mul(q) as u128).rotate_left(5)
}
#[no_mangle]
pub extern "C" fn t_unary(i: u32) -> u64 {
    let x = pick(i);
    let p = x as i128;
    h(x.wrapping_neg())
        ^ h(p.wrapping_abs() as u128).rotate_left(1)
        ^ h(p.unsigned_abs()).rotate_left(2)
        ^ (p.signum() as u64).rotate_left(3)
        ^ (x.leading_zeros() as u64) << 10
        ^ (x.trailing_zeros() as u64) << 20
        ^ (x.count_ones() as u64) << 30
        ^ h(x.isqrt()).rotate_left(5)
        ^ x.checked_ilog10().unwrap_or(99) as u64
        ^ (x.checked_ilog2().unwrap_or(99) as u64) << 40
}
#[no_mangle]
pub extern "C" fn t_euclid(i: u32, j: u32) -> u64 {
    let (p, q) = (pick(i) as i128, pick(j) as i128);
    (match (p.checked_div_euclid(q), p.checked_rem_euclid(q)) {
        (Some(a), Some(b)) => h(a as u128) ^ h(b as u128).rotate_left(7),
        _ => 11,
    }) ^ h(pick(i).abs_diff(pick(j))).rotate_left(9)
        ^ h(p.abs_diff(q)).rotate_left(13)
}
#[no_mangle]
pub extern "C" fn t_all(k: u32) -> u64 {
    // fold every pair for a quick sweep
    let mut r = 0u64;
    let mut i = 0u32;
    while i < 24 {
        let mut j = 0u32;
        while j < 24 {
            r = r.rotate_left(5)
                ^ match k % 4 {
                    0 => t_udiv(i, j),
                    1 => t_sdiv(i, j),
                    2 => t_mul(i, j),
                    _ => t_sat(i, j),
                };
            j += 1;
        }
        i += 1;
    }
    r
}
