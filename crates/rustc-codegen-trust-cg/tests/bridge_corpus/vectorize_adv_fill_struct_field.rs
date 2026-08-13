// OPT-12-FILL adversarial: the fill target is an ARRAY FIELD at a non-zero
// struct offset (a `#[repr(C)]` struct with a leading pad field puts `a` at
// offset 4). The element address is `StackSlot + 4 + i*4`, so the base does not
// trace to a bare `SlotBase` (disp 0) and the recognizer rejects it. Stays
// scalar+correct == LLVM at O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 64;
#[repr(C)]
struct Wrap {
    pad: i32,
    a: [i32; N],
}
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut s = Wrap { pad: bb(9), a: [0i32; N] };
    let mut i = 0usize;
    while i < N { s.a[i] = 0x0055_00aa; i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(s.a[bb(i)] as u32 as u64); i += 1; }
    acc = acc.wrapping_add(s.pad as u32 as u64);
    (acc % 126) as i32
}
