// OPT-12-SAXPY adversarial (THE critical one): cross-element dependence on the
// destination. c[i] = a[i]*k + c[i-1] reads the DEST array `c` at index i-1 (a
// different element than the write at i) — a genuine loop-carried recurrence.
// The `c[i-1]` load's address has index provenance `iv-1` (Unknown), so it is
// NOT `ElemAddr(slot, ELEM_SIZE)` at index iv and fails classification; the
// recognizer bails. This proves the dest==source relaxation is same-index-ONLY:
// any dest access at a different index keeps the loop scalar. Must equal LLVM at
// O0/O2/O3.
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
    while i < N { a[i] = bb(i as i32).wrapping_rem(7).wrapping_add(1); i += 1; }
    c[0] = bb(1i32);
    // c[i] = a[i]*k + c[i-1]  — order-dependent recurrence on the dest array.
    let mut i = 1usize;
    while i < N { c[i] = a[i].wrapping_mul(k).wrapping_add(c[i - 1]); i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(c[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
