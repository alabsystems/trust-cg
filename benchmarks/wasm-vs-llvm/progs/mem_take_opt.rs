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
