// OPT-12-SAXPY positive: element-wise FMA a[i] = a[i]*k + b[i] over i32 arrays,
// k a loop-invariant runtime scalar. The DESTINATION array `a` is BOTH read and
// written, but only ever at the SAME index i (`a[i]` read, `a[i]` written) — no
// cross-element dependence — so the same-index dest==source relaxation applies.
// `b` is a distinct source. The x86 SSE2 vectorizer broadcasts [k;4] once (four
// covered i32 stores into a fresh 16-byte scratch + one MOVDQU load), then per
// packed iter: MOVDQU-load a[i..i+4] -> PMULLD by [k;4] -> MOVDQU-load b[i..i+4]
// -> PADDD -> MOVDQU-store a[i..i+4], for floor(N/4) iters + a scalar remainder.
// PMULLD's per-lane low-32-bit product is bit-for-bit the scalar i32 wrapping
// mul. Must equal LLVM at O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 66; // not a multiple of 4 -> exercises the scalar remainder
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let k = bb(3i32);
    let mut a = [0i32; N];
    let mut b = [0i32; N];
    let mut i = 0usize;
    while i < N { a[i] = (i as i32).wrapping_mul(7).wrapping_add(1); i += 1; }
    let mut i = 0usize;
    while i < N { b[i] = (i as i32).wrapping_mul(13).wrapping_sub(5); i += 1; }
    // saxpy: a[i] = a[i]*k + b[i]  (dest == the multiplied source, same index)
    let mut i = 0usize;
    while i < N { a[i] = a[i].wrapping_mul(k).wrapping_add(b[i]); i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(a[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
