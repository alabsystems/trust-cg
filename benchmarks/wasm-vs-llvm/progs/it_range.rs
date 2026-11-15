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

#[no_mangle]
pub extern "C" fn e_range_top(k: u32) -> u64 {
    let lo = (usize::MAX - (k % 8) as usize) as usize;
    let mut acc = 0u64;
    for i in lo..usize::MAX {
        acc = acc.wrapping_mul(3).wrapping_add(i as u64);
    }
    acc
}
#[no_mangle]
pub extern "C" fn e_range_incl_top(k: u32) -> u64 {
    let lo = usize::MAX - (k % 8) as usize;
    let mut acc = 0u64;
    for i in lo..=usize::MAX {
        acc = acc.wrapping_mul(3).wrapping_add(i as u64);
    }
    acc
}
#[no_mangle]
pub extern "C" fn e_range_len(a: u32, b: u32) -> u64 {
    let r = (a as usize)..(b as usize);
    r.len() as u64 | (r.is_empty() as u64) << 40
}
#[no_mangle]
pub extern "C" fn e_range_sum(a: u32) -> u64 {
    let hi = (a % 100000) as usize;
    (0..hi).map(|x| x as u64).sum::<u64>()
}
#[no_mangle]
pub extern "C" fn e_range_sum_u32(a: u32, b: u32) -> u32 {
    let lo = a;
    let hi = a.saturating_add(b % 64);
    (lo..hi).sum::<u32>()
}
#[no_mangle]
pub extern "C" fn e_range_rev(a: u32) -> u64 {
    let hi = (a % 20) as usize;
    let mut acc = 0u64;
    for i in (0..hi).rev() {
        acc = acc * 31 + i as u64;
    }
    acc
}
#[no_mangle]
pub extern "C" fn e_range_idx(a: u32) -> u32 {
    let lo = (a % 14) as usize;
    (lo..13)
        .map(|i| U8S[i] as u32)
        .fold(0u32, |s, v| s.wrapping_mul(7).wrapping_add(v))
}
#[no_mangle]
pub extern "C" fn e_range_count(a: u32, b: u32) -> u64 {
    let lo = a as usize;
    let hi = lo.saturating_add((b % 1000) as usize);
    (lo..hi).count() as u64 ^ (hi as u64) << 32
}
#[no_mangle]
pub extern "C" fn e_range_i64_neg(a: i64) -> i64 {
    let lo = a.wrapping_sub(3);
    let hi = a.saturating_add(3);
    let mut acc = 0i64;
    for i in lo..hi {
        acc = acc.wrapping_mul(5).wrapping_add(i);
    }
    acc
}
#[no_mangle]
pub extern "C" fn e_range_incl_u8(a: u32) -> u32 {
    let lo = (a as u8).saturating_sub(10);
    let hi = a as u8;
    let mut acc = 0u32;
    for i in lo..=hi {
        acc = acc.wrapping_mul(3).wrapping_add(i as u32);
    }
    acc
}
