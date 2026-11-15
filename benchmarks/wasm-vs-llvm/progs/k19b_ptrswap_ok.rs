#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[inline(never)]
fn swap_idx<T: Copy>(a: &mut [T], i: usize, j: usize) {
    let p = a.as_mut_ptr();
    unsafe { core::ptr::swap(p.add(i), p.add(j)) }
}

#[no_mangle]
pub extern "C" fn pswap_u32(i: u32, j: u32) -> u32 {
    let mut a = [1u32, 2, 3, 4, 5, 6, 7];
    swap_idx(&mut a, (i % 7) as usize, (j % 7) as usize);
    swap_idx(&mut a, (j % 5) as usize, 6);
    a.iter().fold(0, |h, &x| h * 10 + x)
}

#[no_mangle]
pub extern "C" fn pswap_i64(i: u32, j: u32) -> i64 {
    let mut a = [-1i64, 2, i64::MIN, 4, 1 << 40];
    swap_idx(&mut a, (i % 5) as usize, (j % 5) as usize);
    swap_idx(&mut a, 0, (i % 5) as usize);
    a.iter().fold(0i64, |h, &x| h.wrapping_mul(31) ^ x)
}

#[no_mangle]
pub extern "C" fn pswap_u8(i: u32, j: u32) -> u32 {
    let mut a = [1u8, 2, 3, 0xff, 0x80, 6, 7, 8, 9];
    swap_idx(&mut a, (i % 9) as usize, (j % 9) as usize);
    swap_idx(&mut a, (i % 3) as usize, (j % 4) as usize);
    a.iter().fold(0u32, |h, &x| h.wrapping_mul(33) ^ x as u32)
}

#[no_mangle]
pub extern "C" fn pswap_f64(i: u32, j: u32) -> u64 {
    let mut a = [0.5f64, -1.0, 1e300, -0.0];
    swap_idx(&mut a, (i % 4) as usize, (j % 4) as usize);
    a.iter().fold(0u64, |h, &x| h.rotate_left(13) ^ x.to_bits())
}

#[no_mangle]
pub extern "C" fn pswap_u16(i: u32, j: u32) -> u32 {
    let mut a = [0xffffu16, 2, 0x8000, 4, 5, 6];
    swap_idx(&mut a, (i % 6) as usize, (j % 6) as usize);
    a.iter()
        .fold(0u32, |h, &x| h.wrapping_mul(65599) ^ x as u32)
}

#[no_mangle]
pub extern "C" fn mem_take_opt(a: u32, b: u32) -> u64 {
    let mut o = if a & 1 == 0 { Some(a as u64 * 3) } else { None };
    let t = o.take();
    let r = o.replace(b as u64);
    let mut arr = [a, b, a ^ b];
    let tk = core::mem::take(&mut arr[1]);
    t.unwrap_or(5)
        ^ r.map(|x| x + 1).unwrap_or(9) << 1
        ^ (o.unwrap_or(0) << 20)
        ^ (tk as u64) << 40
        ^ (arr[1] as u64 + arr[2] as u64)
}
