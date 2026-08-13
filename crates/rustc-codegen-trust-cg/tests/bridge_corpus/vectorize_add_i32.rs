// OPT-12 positive: element-wise i32 add over THREE distinct local arrays.
// c[i] = a[i] + b[i]. Distinct StackSlots (no alias by construction), write-only
// dest (no loop-carried dep), unit stride 0..N, const N. The x86 SSE2 vectorizer
// rewrites the add loop to MOVDQU loads + PADDD + MOVDQU store for floor(N/4)
// iters + a scalar remainder. Must equal LLVM at O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 66; // not a multiple of 4 -> exercises the scalar remainder
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i32; N];
    let mut b = [0i32; N];
    let mut c = [0i32; N];
    let s = bb(1i32);
    let mut i = 0usize;
    while i < N { a[i] = (i as i32).wrapping_mul(7).wrapping_add(s); i += 1; }
    let mut i = 0usize;
    while i < N { b[i] = (i as i32).wrapping_mul(3).wrapping_sub(s); i += 1; }
    let mut i = 0usize;
    while i < N { c[i] = a[i].wrapping_add(b[i]); i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(c[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
