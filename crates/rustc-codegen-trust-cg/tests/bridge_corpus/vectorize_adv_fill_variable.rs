// OPT-12-FILL adversarial: the fill value is a RUNTIME (black-boxed) value, not
// a compile-time constant. There is no *covered* way to broadcast a non-constant
// (that would need PSHUFD/MOVD, which are not proof-covered), so the fill
// recognizer rejects it and the loop stays scalar+correct == LLVM at O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 64;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i32; N];
    let v = bb(0x2233_4455i32); // runtime -> not a MovRI immediate
    let mut i = 0usize;
    while i < N { a[i] = v; i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(a[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
