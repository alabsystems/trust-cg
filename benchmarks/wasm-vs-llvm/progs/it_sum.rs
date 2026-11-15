#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
static U8S: [u8; 13] = [0, 1, 2, 255, 128, 127, 3, 200, 17, 99, 250, 5, 64];
static U16S: [u16; 9] = [0, 65535, 1, 32768, 4660, 22136, 7, 65534, 300];
static U32S: [u32; 7] = [0xffff_ffff, 1, 0x8000_0000, 12345, 7, 0xdead_beef, 42];
static U64S: [u64; 6] = [
    u64::MAX,
    1,
    0x8000_0000_0000_0000,
    0x1_0000_0000,
    77,
    0xdead_beef_cafe_babe,
];
static I64S: [i64; 6] = [-1, i64::MIN, i64::MAX, -12345678901, 5, 0];
static F64S: [f64; 7] = [0.5, -1.25, 1e300, -1e300, 3.0, 1e-310, 2.5];

#[inline(never)]
fn sum_u8(xs: &[u8]) -> u32 {
    xs.iter().map(|&x| x as u32).sum()
}
#[no_mangle]
pub extern "C" fn e_sum_u8(lo: u32, hi: u32) -> u32 {
    let lo = (lo % 14) as usize;
    let hi = (hi % 14) as usize;
    if lo > hi {
        return 7;
    }
    sum_u8(&U8S[lo..hi])
}
#[inline(never)]
fn wsum_u16(xs: &[u16]) -> u16 {
    xs.iter().fold(0u16, |a, &b| a.wrapping_add(b))
}
#[no_mangle]
pub extern "C" fn e_wsum_u16(n: u32, k: u32) -> u32 {
    let n = (n % 10) as usize;
    let mut loc = U16S;
    loc[(k % 9) as usize] ^= k as u16;
    (wsum_u16(&loc[..n]) as u32) << 1 | (loc.len() as u32) << 20
}
#[inline(never)]
fn sum_u32_ck(xs: &[u32]) -> u32 {
    xs.iter().sum()
}
#[no_mangle]
pub extern "C" fn e_sum_u32_ck(lo: u32, hi: u32) -> u32 {
    let lo = (lo % 8) as usize;
    let hi = (hi % 8) as usize;
    if lo > hi {
        return 3;
    }
    sum_u32_ck(&U32S[lo..hi])
}
#[inline(never)]
fn wsum_u64(xs: &[u64]) -> u64 {
    xs.iter().fold(0u64, |a, b| a.wrapping_add(*b))
}
#[no_mangle]
pub extern "C" fn e_wsum_u64(lo: u32, hi: u32) -> u64 {
    let lo = (lo % 7) as usize;
    let hi = (hi % 7) as usize;
    if lo > hi {
        return 9;
    }
    wsum_u64(&U64S[lo..hi])
}
#[inline(never)]
fn prod_i64(xs: &[i64]) -> i64 {
    xs.iter().fold(1i64, |a, b| a.wrapping_mul(*b))
}
#[no_mangle]
pub extern "C" fn e_prod_i64(lo: u32, x: i64) -> i64 {
    let lo = (lo % 7) as usize;
    let mut arr = I64S;
    arr[5] = x;
    prod_i64(&arr[lo..])
}
#[no_mangle]
pub extern "C" fn e_product_ck(a: u32, b: u32) -> u64 {
    let arr = [
        a as u64 % 100000,
        b as u64 % 100000,
        3u64,
        (a ^ b) as u64 % 1000,
    ];
    arr.iter().product()
}
#[inline(never)]
fn sum_f64(xs: &[f64]) -> f64 {
    xs.iter().sum()
}
#[no_mangle]
pub extern "C" fn e_sum_f64(lo: u32, x: f64) -> f64 {
    let lo = (lo % 8) as usize;
    let mut arr = F64S;
    arr[6] = x;
    sum_f64(&arr[lo..])
}
#[no_mangle]
pub extern "C" fn e_filter_map(k: u32, m: u32) -> u64 {
    let m = m | 1;
    U32S.iter()
        .copied()
        .filter(|x| *x % m != k % m)
        .map(|x| (x as u64) * 3 + 1)
        .fold(0u64, |a, b| a ^ b.rotate_left(7))
}
#[no_mangle]
pub extern "C" fn e_neg_i64(k: i64) -> i64 {
    I64S.iter()
        .map(|&v| v.wrapping_sub(k))
        .filter(|v| *v < 0)
        .fold(0i64, |a, b| a.wrapping_add(b >> 3))
}
#[no_mangle]
pub extern "C" fn e_u8_max_fold(k: u32) -> u32 {
    let mut a = U8S;
    let i = (k % 13) as usize;
    a[i] = a[i].wrapping_add(k as u8);
    a.iter().fold(0u8, |m, &x| if x > m { x } else { m }) as u32
        | (a.iter().copied().filter(|x| *x > 100).count() as u32) << 8
}
