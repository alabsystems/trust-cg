// OPT-12 positive: element-wise i32 bitwise xor over three distinct locals ->
// MOVDQU + PXOR.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 65;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0i32; N];
    let mut b = [0i32; N];
    let mut c = [0i32; N];
    let s = bb(0x5aa5i32);
    let mut i = 0usize;
    while i < N { a[i] = (i as i32).wrapping_mul(2654435761u32 as i32) ^ s; i += 1; }
    let mut i = 0usize;
    while i < N { b[i] = (i as i32).wrapping_mul(40503) ^ s; i += 1; }
    let mut i = 0usize;
    while i < N { c[i] = a[i] ^ b[i]; i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(c[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
