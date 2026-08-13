// OPT-12-SAXPY adversarial: non-invariant multiplier. c[i] = a[i]*alpha + b[i]
// where `alpha` is RECOMPUTED every iteration from the loop index i (IV-
// dependent), so it is NOT loop-invariant. The recognizer's invariance check
// (single-def, def OUTSIDE the loop body, dominates the preheader) fails because
// alpha's def is inside the loop body; it bails. A wrong invariance decision
// would broadcast a stale alpha (a miscompile), so this stays scalar+correct ==
// LLVM at O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 64;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i32; N];
    let mut b = [0i32; N];
    let mut c = [0i32; N];
    let mut i = 0usize;
    while i < N { a[i] = bb(i as i32).wrapping_mul(7); b[i] = bb(i as i32).wrapping_mul(3); i += 1; }
    // alpha varies per iteration (IV-derived) -> not loop-invariant.
    let mut i = 0usize;
    while i < N {
        let alpha = (i as i32).wrapping_mul(2).wrapping_add(1);
        c[i] = a[i].wrapping_mul(alpha).wrapping_add(b[i]);
        i += 1;
    }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(c[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
