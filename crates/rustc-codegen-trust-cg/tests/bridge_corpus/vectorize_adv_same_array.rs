// OPT-12 adversarial: destination is the SAME array as the sources (a==b==c).
// The distinct-StackSlot requirement rejects vectorization (slot_c equals a
// source slot). Element-wise same-index, so it stays scalar+correct == LLVM.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 64;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut buf = [0i32; N];
    let mut i = 0usize;
    while i < N { buf[i] = bb(i as i32).wrapping_mul(3); i += 1; }
    let mut i = 0usize;
    while i < N { let v = buf[i].wrapping_add(buf[i]); buf[i] = v; i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(buf[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
