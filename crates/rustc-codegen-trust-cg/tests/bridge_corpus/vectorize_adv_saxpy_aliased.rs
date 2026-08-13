// OPT-12-SAXPY adversarial: same array aliased at DIFFERENT offsets. The single
// array `a` supplies both the multiplied source (a[i]) and the added source
// (a[i+2]) — same slot, different indices. The `a[i+2]` load's address is not
// `ElemAddr(slot, 4)` at index iv (index provenance `iv+2`, or a non-zero disp),
// so it fails classification and the recognizer bails. This shows that
// dest==source (or source==source) is admitted ONLY when every access is at the
// same index iv; a different-offset access into the same slot is rejected. Stays
// scalar+correct == LLVM at O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 64;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let k = bb(3i32);
    let mut a = [0i32; N];
    let mut c = [0i32; N];
    let mut i = 0usize;
    while i < N { a[i] = bb(i as i32).wrapping_mul(7).wrapping_add(1); i += 1; }
    // c[i] = a[i]*k + a[i+2]  — the added source is the same array, offset by 2.
    let mut i = 0usize;
    while i + 2 < N { c[i] = a[i].wrapping_mul(k).wrapping_add(a[i + 2]); i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(c[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
