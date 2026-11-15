#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
// f15: integer arithmetic on pointer-derived usize values (layout-independent observations only)
static A: [u64; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
static B: [u16; 9] = [1, 2, 3, 4, 5, 6, 7, 8, 9];
#[inline(never)]
fn addr_of<T>(r: &T) -> usize {
    r as *const T as usize
}
#[no_mangle]
pub extern "C" fn addr_diff(i: u32, j: u32) -> i64 {
    let (i, j) = ((i % 8) as usize, (j % 8) as usize);
    let d = addr_of(&A[i]) as isize - addr_of(&A[j]) as isize;
    let e = addr_of(&B[i]).wrapping_sub(addr_of(&B[j]));
    (d as i64) * 1000 + (e as u64 as i64 % 100000) + ((addr_of(&A[i]) % 8) as i64) * 7
}
#[no_mangle]
pub extern "C" fn addr_width(i: u32) -> u64 {
    let a = addr_of(&A[(i % 8) as usize]);
    let x = a as u64;
    let y = a as i64;
    let z = a as u128;
    ((x >> 32 == 0) as u64)
        | ((y >= 0) as u64) << 1
        | (((z >> 32) == 0) as u64) << 2
        | ((a.checked_add(usize::MAX - a).is_some()) as u64) << 3
        | ((a.leading_zeros() < 32) as u64) << 4
        | ((a.wrapping_neg().wrapping_add(a) == 0) as u64) << 5
        | ((a as isize).checked_neg().is_some() as u64) << 6
        | ((a.trailing_zeros() >= 3) as u64) << 16
}
#[no_mangle]
pub extern "C" fn offset_calc(i: u32, j: u32) -> u64 {
    let p = A.as_ptr();
    let n = (i % 8) as usize;
    let m = (j % 8) as usize;
    let q = unsafe { p.add(n) };
    let r = unsafe { p.add(m) };
    let d = unsafe { q.offset_from(r) };
    let bytes = (q as usize).abs_diff(r as usize);
    (d as i64 as u64)
        ^ (bytes as u64) << 20
        ^ unsafe { *q } << 40
        ^ (q.align_offset(8) as u64) << 50
}
#[no_mangle]
pub extern "C" fn byte_offset(i: u32) -> u64 {
    let base = B.as_ptr() as usize;
    let k = (i % 9) as usize;
    let p = (base + k * core::mem::size_of::<u16>()) as *const u16;
    unsafe { *p as u64 + (p as usize - base) as u64 * 100 }
}
