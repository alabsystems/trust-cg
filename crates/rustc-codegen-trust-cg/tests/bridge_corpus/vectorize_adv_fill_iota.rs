// OPT-12-FILL adversarial: the stored value is the loop index (a[i] = i), a
// per-iteration-varying value, not a constant. A fill vectorizer would store the
// SAME 16-byte pattern to every lane, which is wrong here; the recognizer sees
// the value trace to the IV (not a MovRI immediate) and rejects it. Stays
// scalar+correct == LLVM at O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 64;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i32; N];
    let mut i = 0usize;
    while i < N { a[i] = i as i32; i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(a[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
