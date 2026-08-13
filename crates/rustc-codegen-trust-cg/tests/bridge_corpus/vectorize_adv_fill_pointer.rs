// OPT-12-FILL adversarial: the fill goes through a `&mut [i32; N]` REFERENCE
// parameter (an `#[inline(never)]` helper), so the destination base is a pointer
// argument, not a distinct local `Lea [StackSlot]`. Aliasing cannot be ruled out
// by construction, so the recognizer rejects it. Stays scalar+correct == LLVM at
// O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 64;
#[inline(never)]
fn fill(a: &mut [i32; N]) {
    let mut i = 0usize;
    while i < N { a[i] = 0x0102_0304; i += 1; }
}
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i32; N];
    fill(bb(&mut a));
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(a[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
