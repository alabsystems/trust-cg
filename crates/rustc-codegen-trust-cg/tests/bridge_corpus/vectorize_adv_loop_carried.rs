// OPT-12 adversarial: loop-carried dependence c[i] = c[i-1] + a[i]. Reads the
// destination array at index i-1 and the dest slot is also read; both the
// distinctness guard and the same-index guard reject it. Order-dependent
// recurrence stays scalar == LLVM.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 64;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i32; N];
    let mut c = [0i32; N];
    let mut i = 0usize;
    while i < N { a[i] = bb(i as i32).wrapping_rem(7).wrapping_add(1); i += 1; }
    c[0] = bb(1i32);
    let mut i = 1usize;
    while i < N { c[i] = c[i - 1].wrapping_add(a[i]); i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(c[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
