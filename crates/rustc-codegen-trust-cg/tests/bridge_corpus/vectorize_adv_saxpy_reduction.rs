// OPT-12-SAXPY adversarial: dot-product reduction s += a[i]*k. There is no
// element-wise store to an array — the accumulator `s` is loop-carried in a
// register (or a fixed stack slot, not `&slot[iv]`). No `ElemAddr` store at
// index iv is found, so the recognizer bails. Stays scalar+correct == LLVM at
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
    let mut i = 0usize;
    while i < N { a[i] = bb(i as i32).wrapping_mul(3).wrapping_add(1); i += 1; }
    // s += a[i]*k  — horizontal reduction, no array destination.
    let mut s: i32 = bb(0);
    let mut i = 0usize;
    while i < N { s = s.wrapping_add(a[i].wrapping_mul(k)); i += 1; }
    ((s as u32 as u64) % 126) as i32
}
