// OPT-12-SAXPY positive (commuted): y[i] = k*x[i] + y[i] over i32 arrays, k a
// loop-invariant runtime scalar. Here the DESTINATION array `y` coincides with
// the ADDED source (not the multiplied one); `x` is the distinct multiplied
// source. Still same-index-only for `y` (read and written at exactly i), so the
// dest==source relaxation applies. Vectorizes to [k;4] broadcast + PMULLD +
// PADDD + MOVDQU (floor(N/4) iters + scalar remainder). Must equal LLVM at
// O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 70; // not a multiple of 4 -> exercises the scalar remainder
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let k = bb(5i32);
    let mut x = [0i32; N];
    let mut y = [0i32; N];
    let mut i = 0usize;
    while i < N { x[i] = (i as i32).wrapping_mul(3).wrapping_add(2); i += 1; }
    let mut i = 0usize;
    while i < N { y[i] = (i as i32).wrapping_mul(11).wrapping_sub(7); i += 1; }
    // y[i] = k*x[i] + y[i]  (dest == the added source, same index)
    let mut i = 0usize;
    while i < N { y[i] = k.wrapping_mul(x[i]).wrapping_add(y[i]); i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(y[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
