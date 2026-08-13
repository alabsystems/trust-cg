// OPT-12-REDUCE adversarial: a NON-ASSOCIATIVE integer reduction
// s = s.rotate_left(1) ^ a[i]. The combine is not a plain wrapping add (it mixes
// a rotate with an xor and is order-dependent), so lane-partials + combine would
// NOT equal the sequential fold. The recognizer only admits the integer wrapping
// add `AddRR` as the reduction op; the accumulator's in-body update here is not
// `AddRR(acc, term)`, so it is rejected and stays scalar+correct == LLVM at
// O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 66;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i32; N];
    let mut i = 0usize;
    while i < N { a[i] = bb(i as i32).wrapping_mul(5).wrapping_add(2); i += 1; }
    let mut s: u32 = bb(1u32);
    let mut i = 0usize;
    while i < N { s = s.rotate_left(1) ^ (a[i] as u32); i += 1; }
    ((s as u64) % 126) as i32
}
