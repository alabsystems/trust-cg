// OPT-12 positive: element-wise i32 subtract (NON-commutative: order matters).
// c[i] = a[i] - b[i] over three distinct local arrays -> MOVDQU + PSUBD.
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
    let s = bb(2i32);
    let mut i = 0usize;
    while i < N { a[i] = (i as i32).wrapping_mul(11).wrapping_add(s); i += 1; }
    let mut i = 0usize;
    while i < N { b[i] = (i as i32).wrapping_mul(5).wrapping_sub(s); i += 1; }
    let mut i = 0usize;
    while i < N { c[i] = a[i].wrapping_sub(b[i]); i += 1; }
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < N { acc = acc.wrapping_add(c[bb(i)] as u32 as u64); i += 1; }
    (acc % 126) as i32
}
