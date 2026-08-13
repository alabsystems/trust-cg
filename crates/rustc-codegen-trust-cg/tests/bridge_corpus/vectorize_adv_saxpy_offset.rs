// OPT-12-SAXPY adversarial: offset source index. c[i] = a[i]*k + b[i+1] reads
// the added source `b` at index i+1, a different element than the destination
// write at i. The `b[i+1]` load's address is `&slot[iv] + 4` (non-zero disp) or
// has index provenance `iv+1` (not `Iv`), so it is not `ElemAddr(slot, 4)` at
// index iv and fails classification; the recognizer bails. Stays scalar+correct
// == LLVM at O0/O2/O3.
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
    let mut b = [0i32; N];
    let mut c = [0i32; N];
    let mut i = 0usize;
    while i < N { a[i] = bb(i as i32).wrapping_mul(7); b[i] = bb(i as i32).wrapping_mul(3); i += 1; }
    // c[i] = a[i]*k + b[i+1]  — added source at a different index.
    let mut i = 0usize;
    while i + 1 < N { c[i] = a[i].wrapping_mul(k).wrapping_add(b[i + 1]); i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(c[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
